from __future__ import annotations

import json
import unittest
from unittest.mock import patch

from archon.commands.loop.review_feedback import (
    MAX_REPAIR_TASK_PROMPT_BYTES,
    bound_repair_task,
    build_feedback_event,
    build_repair_task,
    render_repair_task,
    sanitized_review_history,
    safe_preflight_summary,
)


def _source_bound_formalization_certificate(
    candidate_sha256: str,
) -> dict:
    passed = {"status": "passed", "evidence": "source-bound check passed"}
    return {
        "schema_version": 2,
        "status": "failed",
        "reason": "PANEL_SWAP_DIAGNOSIS",
        "checks": {
            "source_faithfulness": {
                "status": "failed",
                "evidence": "PANEL_LABEL_AND_TOPOLOGY_EVIDENCE",
            },
            "derivability": {
                "status": "failed",
                "evidence": "SOURCE_FIRST_COMPONENT_LEDGER_EVIDENCE",
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
        "bridge_obligations": [{
            "claim": "SOURCE_BOUND_REPAIR_CLAIM",
            "carrier": "CURRENT_WRONG_CARRIER",
            "status": "blocked",
            "evidence": "SOURCE_TO_LEAN_BRIDGE_DIAGNOSIS",
        }],
        "source_contract": {
            "schema_version": 1,
            "contract_kind": "native_problem_input_only",
            "authority": "problem-only",
            "evaluation_mode": "answer_blind",
            "target": "IChO2026Problems/A.lean",
            "source_bundle": "icho_2026_source/questions_only.jsonl",
            "source_record_id": "problem_a",
            "candidate": "IChO2026Problems/A.lean",
            "candidate_sha256": candidate_sha256,
            "source_bundle_sha256": "1" * 64,
            "source_record_sha256": "2" * 64,
            "answer_submission_sha256": "3" * 64,
            "question_sha256": "4" * 64,
            "requested_outputs_sha256": "5" * 64,
        },
        "blind_source_audit": {
            "answer_independence": {
                "status": "passed",
                "evidence": "ANSWER_INDEPENDENCE_ATTESTATION_SECRET",
            },
            "raw_derivation": {
                "status": "passed",
                "evidence": "UNPROJECTED_RAW_DERIVATION_SECRET",
            },
        },
        "requested_outputs": [{
            "source_requirement": "UNPROJECTED_REQUESTED_OUTPUT_SECRET",
            "status": "blocked",
            "evidence": "UNPROJECTED_OUTPUT_EVIDENCE_SECRET",
        }],
        "chemistry_checks": {
            "chemical_semantics": {
                "status": "failed",
                "evidence": "UNPROJECTED_CHEMISTRY_SECRET",
            },
        },
    }


class ReviewFeedbackTest(unittest.TestCase):
    def test_proof_feedback_is_structured_and_answer_free(self) -> None:
        digest = "a" * 64
        certificate = {
            "blind_source_audit": {
                "lean_result_binding": {
                    "status": "failed",
                    "evidence": "EXPECTED_RESULT_SECRET",
                },
            },
            "contract_audit": {
                "statement_scope": {
                    "status": "passed",
                    "evidence": "RAW_SCOPE_SECRET",
                },
            },
            "requested_outputs": [{
                "source_requirement": "RESULT_SPEC_SECRET",
                "status": "blocked",
                "evidence": "RAW_OUTPUT_SECRET",
            }],
            "result_spec": {"value": "TOP_LEVEL_RESULT_SECRET"},
        }
        event = build_feedback_event(
            review_kind="proof",
            candidate_sha256=digest,
            event_id="pipeline:1:A.lean:proof:1",
            iteration=1,
            attempt=1,
            resulting_status="retry",
            certificate=certificate,
            route="retry_proof",
            redraft_kind="not_applicable",
            preflight={
                "status": "timeout",
                "compiles": False,
                "returncode": None,
                "sorry_count": 0,
                "duration_secs": 300.125,
                "diagnostics": "LEAN_DIAGNOSTIC_SECRET",
                "file": "ANSWER_BEARING_PATH_SECRET",
            },
        )

        self.assertEqual(event["candidate_sha256"], digest)
        self.assertEqual(event["route"], "retry_proof")
        failed = event["failed_check_ids"]
        self.assertIn("blind_source_audit.lean_result_binding", failed)
        self.assertIn("requested_outputs[0]", failed)
        self.assertIn("blind_source_audit.answer_independence", failed)
        self.assertIn("contract_audit.bridge_completeness", failed)
        self.assertEqual(event["preflight"]["status"], "timeout")
        payload = json.dumps(event)
        for secret in (
            "EXPECTED_RESULT_SECRET",
            "RAW_SCOPE_SECRET",
            "RESULT_SPEC_SECRET",
            "RAW_OUTPUT_SECRET",
            "TOP_LEVEL_RESULT_SECRET",
            "LEAN_DIAGNOSTIC_SECRET",
            "ANSWER_BEARING_PATH_SECRET",
        ):
            self.assertNotIn(secret, payload)
        self.assertNotIn("result_spec", payload)

    def test_requested_output_answer_audit_mismatches_are_index_only(self) -> None:
        for field in ("submission_status", "reporting_policy_status"):
            with self.subTest(field=field):
                output = {
                    "output_id": "SECRET_OUTPUT_ID",
                    "source_requirement": "SECRET_REQUIREMENT",
                    "status": "covered",
                    "submission_status": "matched",
                    "reporting_policy_status": "matched",
                    "lean_carrier": "SECRET_CARRIER",
                    "evidence": "SECRET_EVIDENCE",
                }
                output[field] = "failed"
                event = build_feedback_event(
                    review_kind="proof",
                    candidate_sha256="e" * 64,
                    event_id="pipeline:1:A.lean:proof:1",
                    iteration=1,
                    attempt=1,
                    resulting_status="retry",
                    certificate={"requested_outputs": [output]},
                    route="retry_proof",
                    redraft_kind="not_applicable",
                )
                self.assertIn(
                    "requested_outputs[0]", event["failed_check_ids"]
                )
                payload = json.dumps(event)
                for secret in (
                    "SECRET_OUTPUT_ID",
                    "SECRET_REQUIREMENT",
                    "SECRET_CARRIER",
                    "SECRET_EVIDENCE",
                ):
                    self.assertNotIn(secret, payload)

    def test_component_accounting_failure_handoff_is_parent_index_only(
        self,
    ) -> None:
        output = {
            "output_id": "SECRET_COMPONENT_OUTPUT_ID",
            "source_requirement": "SECRET_COMPONENT_REQUIREMENT",
            "status": "covered",
            "submission_status": "matched",
            "reporting_policy_status": "matched",
            "lean_carrier": "SECRET_COMPONENT_CARRIER",
            "evidence": "SECRET_PARENT_EVIDENCE",
            "composition_accounting": {
                "source_images": [{
                    "path": "SECRET_IMAGE_PATH",
                    "sha256": "f" * 64,
                }],
                "product_nodes": [{
                    "node_id": "SECRET_TOPOLOGY_NODE_ID",
                    "node_kind": "repeat_unit",
                    "formula_or_descriptor": "SECRET_TOPOLOGY_NODE_FORMULA",
                    "source_path": "SECRET_TOPOLOGY_SOURCE_PATH",
                    "source_locator": "SECRET_TOPOLOGY_NODE_LOCATOR",
                    "multiplicity": 314159,
                }],
                "assembly_edges": [{
                    "edge_id": "SECRET_TOPOLOGY_EDGE_ID",
                    "from_node_id": "SECRET_TOPOLOGY_FROM_ID",
                    "to_node_id": "SECRET_TOPOLOGY_TO_ID",
                    "relation": "covalent_bond",
                    "multiplicity": 161803,
                }],
                "boundary_checks": [{
                    "boundary_id": "SECRET_BOUNDARY_ID",
                    "boundary_kind": "cross_boundary_bond",
                    "source_path": "SECRET_BOUNDARY_SOURCE_PATH",
                    "source_locator": "SECRET_BOUNDARY_LOCATOR",
                    "disposition": "represented_by_edge",
                    "assembly_edge_id": "SECRET_BOUNDARY_EDGE_ID",
                    "status": "ambiguous",
                }],
                "components": [{
                    "product_node_id": "SECRET_COMPONENT_NODE_REF",
                    "label": "SECRET_COMPONENT_LABEL",
                    "formula_or_descriptor": "SECRET_COMPONENT_FORMULA",
                    "multiplicity": 271828,
                    "role": "repeat_unit",
                }],
                "assembly_expression": "SECRET_ASSEMBLY_EXPRESSION",
                "combined_formula_or_quantity": "SECRET_COMBINED_FORMULA",
                "lean_carrier": "SECRET_COMPONENT_CARRIER",
                "status": "failed",
                "evidence": "SECRET_COMPONENT_EVIDENCE",
            },
        }
        event = build_feedback_event(
            review_kind="proof",
            candidate_sha256="9" * 64,
            event_id="pipeline:1:A.lean:proof:1",
            iteration=1,
            attempt=1,
            resulting_status="retry",
            certificate={"requested_outputs": [output]},
            route="retry_proof",
            redraft_kind="other_modeling_defect",
        )
        self.assertIn("requested_outputs[0]", event["failed_check_ids"])
        payload = json.dumps(event)
        for secret in (
            "SECRET_COMPONENT_OUTPUT_ID",
            "SECRET_COMPONENT_REQUIREMENT",
            "SECRET_COMPONENT_CARRIER",
            "SECRET_PARENT_EVIDENCE",
            "SECRET_IMAGE_PATH",
            "SECRET_TOPOLOGY_NODE_ID",
            "SECRET_TOPOLOGY_NODE_FORMULA",
            "SECRET_TOPOLOGY_SOURCE_PATH",
            "SECRET_TOPOLOGY_NODE_LOCATOR",
            "314159",
            "SECRET_TOPOLOGY_EDGE_ID",
            "SECRET_TOPOLOGY_FROM_ID",
            "SECRET_TOPOLOGY_TO_ID",
            "161803",
            "SECRET_BOUNDARY_ID",
            "SECRET_BOUNDARY_SOURCE_PATH",
            "SECRET_BOUNDARY_LOCATOR",
            "SECRET_BOUNDARY_EDGE_ID",
            "SECRET_COMPONENT_NODE_REF",
            "SECRET_COMPONENT_LABEL",
            "SECRET_COMPONENT_FORMULA",
            "271828",
            "SECRET_ASSEMBLY_EXPRESSION",
            "SECRET_COMBINED_FORMULA",
            "SECRET_COMPONENT_EVIDENCE",
        ):
            self.assertNotIn(secret, payload)
        self.assertNotIn("composition_accounting", payload)

    def test_legacy_history_keeps_routes_but_drops_free_text(self) -> None:
        record = {
            "status": "retry",
            "attempts": 1,
            "reason": "TOP_LEVEL_SECRET",
            "evidence": "TOP_LEVEL_EVIDENCE_SECRET",
            "history": [{
                "event_id": "proof-event-1",
                "iter": 1,
                "attempt": 1,
                "route": "retry_proof",
                "resulting_status": "retry",
                "redraft_kind": "not_applicable",
                "reason": "HISTORY_REASON_SECRET",
                "evidence": "HISTORY_EVIDENCE_SECRET",
                "result_spec": {"value": "HISTORY_RESULT_SECRET"},
            }],
        }
        history = sanitized_review_history(record, review_kind="proof")
        self.assertNotIn("event_id", history["events"][0])
        self.assertEqual(history["events"][0]["route"], "retry_proof")
        payload = json.dumps(history)
        self.assertNotIn("proof-event-1", payload)
        for secret in (
            "TOP_LEVEL_SECRET",
            "TOP_LEVEL_EVIDENCE_SECRET",
            "HISTORY_REASON_SECRET",
            "HISTORY_EVIDENCE_SECRET",
            "HISTORY_RESULT_SECRET",
        ):
            self.assertNotIn(secret, payload)

    def test_repair_task_uses_bound_event_and_safe_preflight(self) -> None:
        digest = "b" * 64
        event = build_feedback_event(
            review_kind="proof",
            candidate_sha256=digest,
            event_id="proof-event-2",
            iteration=2,
            attempt=2,
            resulting_status="retry",
            certificate={
                "contract_audit": {
                    "bridge_completeness": {
                        "status": "failed",
                        "evidence": "BRIDGE_ANSWER_SECRET",
                    },
                },
            },
            route="retry_proof",
            redraft_kind="not_applicable",
            preflight={
                "status": "timeout",
                "compiles": False,
                "returncode": None,
                "sorry_count": 0,
                "duration_secs": 3600.0,
            },
        )
        record = {
            "status": "retry",
            "candidate_sha256": digest,
            "attempts": 2,
            "proof_review_route": "retry_proof",
            "repair_events": [event],
            "reason": "RAW_REASON_SECRET",
            "evidence": "RAW_EVIDENCE_SECRET",
        }
        task = build_repair_task(
            record,
            review_kind="proof",
            worker_stage="proof",
            candidate_sha256=digest,
        )
        self.assertEqual(task["candidate_sha256"], digest)
        self.assertIn("deterministic_preflight_timeout", task["reason_codes"])
        self.assertIn(
            "contract_audit.bridge_completeness", task["failed_check_ids"]
        )
        self.assertIn(
            "reduce_elaboration_and_kernel_checking_cost",
            task["required_actions"],
        )
        self.assertNotIn(
            "make_the_current_candidate_compile", task["required_actions"]
        )
        payload = json.dumps(task)
        for secret in (
            "BRIDGE_ANSWER_SECRET", "RAW_REASON_SECRET", "RAW_EVIDENCE_SECRET",
        ):
            self.assertNotIn(secret, payload)


    def test_feedback_event_requires_valid_nonempty_candidate_sha(self) -> None:
        with self.assertRaises(ValueError):
            build_feedback_event(
                review_kind="proof",
                candidate_sha256="",
                event_id="",
                iteration=0,
                attempt=0,
                resulting_status="retry",
                certificate={},
            )


    def test_preflight_summary_is_empty_or_fixed_structure_only(self) -> None:
        self.assertEqual(safe_preflight_summary(None), {})
        self.assertEqual(safe_preflight_summary({}), {})
        summary = safe_preflight_summary({
            "status": "timeout",
            "compiles": False,
            "returncode": None,
            "sorry_count": 0,
            "duration_secs": 61.0,
            "diagnostics": "DIAGNOSTIC_SECRET",
            "file": "ANSWER_PATH_SECRET",
        })
        self.assertEqual(summary["status"], "timeout")
        self.assertEqual(summary["duration_bucket"], "1_to_5m")
        payload = json.dumps(summary)
        self.assertNotIn("DIAGNOSTIC_SECRET", payload)
        self.assertNotIn("ANSWER_PATH_SECRET", payload)


    def test_stale_event_is_not_rebound_and_text_channels_are_dropped(self) -> None:
        current_digest = "c" * 64
        stale_digest = "d" * 64
        event = {
            "schema_version": 1,
            "review_kind": "proof",
            "candidate_sha256": stale_digest,
            "iteration": 3,
            "attempt": 1,
            "resulting_status": "retry",
            "route": "retry_proof",
            "redraft_kind": "not_applicable",
            "failed_check_ids": ["contract_audit.bridge_completeness", "answer_314159"],
            "event_id": "EVENT_ID_ANSWER_SECRET",
            "reason": "RAW_REASON_SECRET",
            "evidence": "RAW_EVIDENCE_SECRET",
            "result_spec": {"value": "RAW_RESULT_SECRET"},
        }
        record = {
            "candidate_sha256": current_digest,
            "status": "retry",
            "repair_events": [event],
            "reason": "TOP_LEVEL_REASON_SECRET",
        }
        task = build_repair_task(
            record,
            review_kind="proof",
            worker_stage="proof",
            candidate_sha256=current_digest,
        )
        self.assertEqual(task, {})
        history = sanitized_review_history(record, review_kind="proof")
        payload = json.dumps(history)
        self.assertNotIn("answer_314159", payload)
        self.assertNotIn("EVENT_ID_ANSWER_SECRET", payload)
        self.assertNotIn("RAW_REASON_SECRET", payload)
        self.assertNotIn("RAW_EVIDENCE_SECRET", payload)
        self.assertNotIn("RAW_RESULT_SECRET", payload)
        self.assertIn("contract_audit.bridge_completeness", payload)


    def test_resume_can_drop_stale_record_but_default_stays_fail_closed(self) -> None:
        old_digest = "1" * 64
        current_digest = "2" * 64
        record = {
            "candidate_sha256": old_digest,
            "status": "retry",
            "proof_review_route": "retry_proof",
        }

        with self.assertRaisesRegex(ValueError, "does not match gate record"):
            build_repair_task(
                record,
                review_kind="proof",
                worker_stage="proof",
                candidate_sha256=current_digest,
            )
        self.assertEqual(
            build_repair_task(
                record,
                review_kind="proof",
                worker_stage="proof",
                candidate_sha256=current_digest,
                discard_stale_record=True,
            ),
            {},
        )
        with self.assertRaisesRegex(ValueError, "lowercase SHA-256"):
            build_repair_task(
                record,
                review_kind="proof",
                worker_stage="proof",
                candidate_sha256="not-a-digest",
                discard_stale_record=True,
            )


    def test_solved_review_never_generates_a_repair_task(self) -> None:
        digest = "e" * 64
        event = build_feedback_event(
            review_kind="proof",
            candidate_sha256=digest,
            event_id="proof-solved",
            iteration=4,
            attempt=1,
            resulting_status="solved",
            certificate={},
            route="solved",
            preflight={"status": "timeout", "compiles": False},
        )
        record = {"candidate_sha256": digest, "status": "solved", "repair_events": [event]}
        self.assertEqual(
            build_repair_task(
                record,
                review_kind="proof",
                worker_stage="proof",
                candidate_sha256=digest,
            ),
            {},
        )


    def test_formalization_redraft_gets_only_bound_review_diagnosis(self) -> None:
        digest = "6" * 64
        certificate = _source_bound_formalization_certificate(digest)
        event = build_feedback_event(
            review_kind="formalization",
            candidate_sha256=digest,
            event_id="formalization-event-1",
            iteration=1,
            attempt=1,
            resulting_status="retry",
            certificate=certificate,
            decision="failed",
            preflight={
                "status": "passed",
                "compiles": True,
                "returncode": 0,
                "sorry_count": 8,
            },
        )
        record = {
            "status": "retry",
            "candidate_sha256": digest,
            "certificate": certificate,
            "repair_events": [event],
        }

        unbound = build_repair_task(
            record,
            review_kind="formalization",
            worker_stage="formalization",
            candidate_sha256=digest,
        )
        self.assertNotIn("source_bound_review", unbound)

        with patch(
            "archon.commands.loop.review_feedback."
            "validate_native_review_source_certificate",
            return_value="",
        ):
            task = build_repair_task(
                record,
                review_kind="formalization",
                worker_stage="formalization",
                candidate_sha256=digest,
                expected_source_contract={
                    "contract_kind": "native_problem_input_only",
                },
            )

        review = task["source_bound_review"]
        self.assertEqual(review["source_binding"]["candidate_sha256"], digest)
        self.assertEqual(
            review["source_binding"]["source_record_sha256"], "2" * 64
        )
        self.assertRegex(review["certificate_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(review["source_contract_sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(review["reason"], "PANEL_SWAP_DIAGNOSIS")
        self.assertEqual(
            review["repair_actions"][0],
            {
                "check_id": "bridge_obligations[0]",
                "source_claim": "SOURCE_BOUND_REPAIR_CLAIM",
                "current_carrier": "CURRENT_WRONG_CARRIER",
                "evidence": "SOURCE_TO_LEAN_BRIDGE_DIAGNOSIS",
            },
        )
        self.assertNotIn("open_proof_holes", task["reason_codes"])
        self.assertNotIn("close_all_open_proof_holes", task["required_actions"])
        payload = json.dumps(task)
        for secret in (
            "ANSWER_INDEPENDENCE_ATTESTATION_SECRET",
            "UNPROJECTED_RAW_DERIVATION_SECRET",
            "UNPROJECTED_REQUESTED_OUTPUT_SECRET",
            "UNPROJECTED_OUTPUT_EVIDENCE_SECRET",
            "UNPROJECTED_CHEMISTRY_SECRET",
        ):
            self.assertNotIn(secret, payload)
        self.assertLessEqual(
            len(json.dumps(review, ensure_ascii=False).encode("utf-8")),
            24 * 1024,
        )

    def test_source_bound_review_projection_fails_closed(self) -> None:
        digest = "7" * 64
        cases: list[tuple[str, dict]] = []

        missing_binding = _source_bound_formalization_certificate(digest)
        missing_binding["source_contract"].pop("source_record_sha256")
        cases.append(("missing source hash", missing_binding))

        stale_candidate = _source_bound_formalization_certificate(digest)
        stale_candidate["source_contract"]["candidate_sha256"] = "8" * 64
        cases.append(("stale candidate", stale_candidate))

        independence_failed = _source_bound_formalization_certificate(digest)
        independence_failed["blind_source_audit"]["answer_independence"][
            "status"
        ] = "failed"
        cases.append(("answer independence failed", independence_failed))

        forbidden_value = _source_bound_formalization_certificate(digest)
        forbidden_value["requested_outputs"][0][
            "display_value"
        ] = "OFFICIAL_VALUE_SECRET"
        cases.append(("forbidden expected-value field", forbidden_value))

        malformed_official_seen = _source_bound_formalization_certificate(digest)
        malformed_official_seen["source_contract"]["official_answer_seen"] = []
        cases.append(("malformed official answer flag", malformed_official_seen))

        nonfinite_extension = _source_bound_formalization_certificate(digest)
        nonfinite_extension["unselected_metric"] = float("nan")
        cases.append(("nonfinite certificate extension", nonfinite_extension))

        oversized_field = _source_bound_formalization_certificate(digest)
        oversized_field["checks"]["source_faithfulness"]["evidence"] = (
            "x" * 2_049
        )
        cases.append(("oversized evidence", oversized_field))

        oversized_certificate = _source_bound_formalization_certificate(digest)
        oversized_certificate["unselected_notes"] = "x" * (256 * 1024)
        cases.append(("oversized certificate", oversized_certificate))

        for label, certificate in cases:
            with self.subTest(label=label):
                event = build_feedback_event(
                    review_kind="formalization",
                    candidate_sha256=digest,
                    event_id=f"formalization-{label.replace(' ', '-')}",
                    iteration=1,
                    attempt=1,
                    resulting_status="retry",
                    certificate=certificate,
                    decision="failed",
                )
                record = {
                    "status": "retry",
                    "candidate_sha256": digest,
                    "certificate": certificate,
                    "repair_events": [event],
                }
                with patch(
                    "archon.commands.loop.review_feedback."
                    "validate_native_review_source_certificate",
                    return_value="",
                ):
                    task = build_repair_task(
                        record,
                        review_kind="formalization",
                        worker_stage="formalization",
                        candidate_sha256=digest,
                        expected_source_contract={
                            "contract_kind": "native_problem_input_only",
                        },
                    )
                self.assertNotIn("source_bound_review", task)
                self.assertNotIn("OFFICIAL_VALUE_SECRET", json.dumps(task))

    def test_many_bridges_are_validated_and_blocked_first_byte_bounded(
        self,
    ) -> None:
        digest = "8" * 64

        def repair_task(certificate: dict) -> dict:
            event = build_feedback_event(
                review_kind="formalization",
                candidate_sha256=digest,
                event_id="formalization-many-bridges",
                iteration=1,
                attempt=1,
                resulting_status="retry",
                certificate=certificate,
                decision="failed",
            )
            record = {
                "status": "retry",
                "candidate_sha256": digest,
                "certificate": certificate,
                "repair_events": [event],
            }
            with patch(
                "archon.commands.loop.review_feedback."
                "validate_native_review_source_certificate",
                return_value="",
            ):
                return build_repair_task(
                    record,
                    review_kind="formalization",
                    worker_stage="formalization",
                    candidate_sha256=digest,
                    expected_source_contract={
                        "contract_kind": "native_problem_input_only",
                    },
                )

        cycle_three_shape = _source_bound_formalization_certificate(digest)
        cycle_three_shape["bridge_obligations"] = [
            {
                "claim": f"anonymized source claim {index}",
                "carrier": f"anonymized_carrier_{index}",
                "status": (
                    "failed"
                    if index == 0
                    else "blocked"
                    if index >= 15
                    else "covered"
                ),
                "evidence": f"anonymized source evidence {index}",
            }
            for index in range(21)
        ]
        task = repair_task(cycle_three_shape)
        review = task["source_bound_review"]
        projection = review["repair_action_projection"]
        self.assertEqual(projection["bridge_obligations_count"], 21)
        self.assertEqual(projection["failed_bridge_count"], 7)
        self.assertEqual(projection["retained_count"], 7)
        self.assertFalse(projection["truncated"])
        self.assertRegex(
            projection["bridge_obligations_sha256"], r"^[0-9a-f]{64}$"
        )
        self.assertEqual(
            review["repair_actions"][0]["check_id"],
            "bridge_obligations[15]",
        )
        self.assertEqual(
            review["repair_actions"][-1]["check_id"],
            "bridge_obligations[0]",
        )

        invalid_late_bridge = json.loads(json.dumps(cycle_three_shape))
        invalid_late_bridge["bridge_obligations"][20]["evidence"] = (
            "x" * 2_049
        )
        invalid_task = repair_task(invalid_late_bridge)
        self.assertNotIn("source_bound_review", invalid_task)

        oversized = _source_bound_formalization_certificate(digest)
        oversized["bridge_obligations"] = [
            {
                "claim": f"{index}:" + "c" * 1_190,
                "carrier": f"{index}:" + "k" * 790,
                "status": "blocked",
                "evidence": f"{index}:" + "e" * 2_038,
            }
            for index in range(21)
        ]
        bounded_task = repair_task(oversized)
        bounded_review = bounded_task["source_bound_review"]
        bounded_projection = bounded_review["repair_action_projection"]
        self.assertEqual(bounded_projection["bridge_obligations_count"], 21)
        self.assertEqual(bounded_projection["failed_bridge_count"], 21)
        self.assertLess(bounded_projection["retained_count"], 21)
        self.assertTrue(bounded_projection["truncated"])
        self.assertEqual(
            bounded_review["repair_actions"][0]["check_id"],
            "bridge_obligations[0]",
        )
        self.assertEqual(
            bounded_projection["retained_count"],
            len(bounded_review["repair_actions"]),
        )
        self.assertLessEqual(
            len(render_repair_task(bounded_task).encode("utf-8")),
            MAX_REPAIR_TASK_PROMPT_BYTES,
        )

    def test_open_sorry_action_is_proof_worker_only(self) -> None:
        digest = "9" * 64
        certificate = {
            "contract_audit": {
                "bridge_completeness": {
                    "status": "failed",
                    "evidence": "PROOF_REVIEW_EVIDENCE_SECRET",
                },
            },
        }
        event = build_feedback_event(
            review_kind="proof",
            candidate_sha256=digest,
            event_id="proof-open-sorry",
            iteration=1,
            attempt=1,
            resulting_status="retry",
            certificate=certificate,
            route="retry_proof",
            redraft_kind="not_applicable",
            preflight={
                "status": "passed",
                "compiles": True,
                "returncode": 0,
                "sorry_count": 2,
            },
        )
        record = {
            "status": "retry",
            "candidate_sha256": digest,
            "proof_review_route": "retry_proof",
            "repair_events": [event],
        }
        task = build_repair_task(
            record,
            review_kind="proof",
            worker_stage="proof",
            candidate_sha256=digest,
        )
        self.assertIn("open_proof_holes", task["reason_codes"])
        self.assertIn("close_all_open_proof_holes", task["required_actions"])

        proof_to_formalization = build_repair_task(
            record,
            review_kind="proof",
            worker_stage="formalization",
            candidate_sha256=digest,
        )
        self.assertNotIn(
            "open_proof_holes", proof_to_formalization["reason_codes"]
        )
        self.assertNotIn(
            "close_all_open_proof_holes",
            proof_to_formalization["required_actions"],
        )

        formal_certificate = _source_bound_formalization_certificate(digest)
        formal_event = build_feedback_event(
            review_kind="formalization",
            candidate_sha256=digest,
            event_id="formalization-open-sorry",
            iteration=1,
            attempt=1,
            resulting_status="retry",
            certificate=formal_certificate,
            decision="failed",
            preflight={
                "status": "passed",
                "compiles": True,
                "returncode": 0,
                "sorry_count": 2,
            },
        )
        formal_record = {
            "status": "retry",
            "candidate_sha256": digest,
            "certificate": formal_certificate,
            "repair_events": [formal_event],
        }
        expected_contract = {
            "contract_kind": "native_problem_input_only",
        }
        with patch(
            "archon.commands.loop.review_feedback."
            "validate_native_review_source_certificate",
            return_value="",
        ):
            formal_to_formalization = build_repair_task(
                formal_record,
                review_kind="formalization",
                worker_stage="formalization",
                candidate_sha256=digest,
                expected_source_contract=expected_contract,
            )
            formal_to_proof = build_repair_task(
                formal_record,
                review_kind="formalization",
                worker_stage="proof",
                candidate_sha256=digest,
                expected_source_contract=expected_contract,
            )
        self.assertIn("source_bound_review", formal_to_formalization)
        self.assertNotIn(
            "open_proof_holes", formal_to_formalization["reason_codes"]
        )
        self.assertNotIn(
            "close_all_open_proof_holes",
            formal_to_formalization["required_actions"],
        )
        self.assertNotIn("source_bound_review", formal_to_proof)
        self.assertIn("open_proof_holes", formal_to_proof["reason_codes"])
        self.assertIn(
            "close_all_open_proof_holes", formal_to_proof["required_actions"]
        )

    def test_repair_task_uses_exact_bounded_renderer(self) -> None:
        task = {
            "schema_version": 1,
            "history": {
                "events": [
                    {"event_id": str(index), "reason_codes": ["x" * 200]}
                    for index in range(20)
                ],
            },
            "source_bound_review": {
                "repair_actions": [
                    {"check_id": str(index), "evidence": "é" * 200}
                    for index in range(20)
                ],
            },
        }
        bounded = bound_repair_task(task, maximum_bytes=512)
        rendered = render_repair_task(bounded)
        self.assertEqual(json.loads(rendered), bounded)
        self.assertLessEqual(len(rendered.encode("utf-8")), 512)
        self.assertEqual(
            bound_repair_task(task, maximum_bytes=1),
            {},
        )
        self.assertEqual(MAX_REPAIR_TASK_PROMPT_BYTES, 24 * 1024)


if __name__ == "__main__":
    unittest.main()
