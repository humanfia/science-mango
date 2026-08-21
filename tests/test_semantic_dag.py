from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path
from unittest.mock import patch

from archon.commands.loop.problem_only_review_contract import (
    render_native_formalizer_semantic_dag_prompt,
)
from archon.commands.loop.prover.runners import (
    _native_formalizer_semantic_dag_block,
    build_immediate_redraft_prompt,
)
from archon.commands.loop.semantic_dag import (
    SemanticDagError,
    build_semantic_dag,
    render_solver_semantic_dag_prompt,
    semantic_dag_provenance,
)


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

    def test_immediate_redraft_prompt_contains_semantic_dag(self) -> None:
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "select_prover_mode_for_target",
                return_value="chemistry-formalize",
            ),
            patch(
                "archon.commands.loop.prover.runners._load_mode_content",
                return_value=None,
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

    def test_immediate_redraft_prompt_enforces_real_utf8_boundary(self) -> None:
        oversized_task = {
            "failed_check_ids": ["coverage"],
            "history": {
                "events": [
                    {"event_id": str(index), "codes": ["历史" * 200]}
                    for index in range(20)
                ],
            },
            "source_bound_review": {
                "reason": "panel topology mismatch",
                "repair_actions": [
                    {
                        "check_id": f"repair-{index}",
                        "evidence": "证据" * 120,
                    }
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
                "archon.commands.loop.prover.runners._load_mode_content",
                return_value=None,
            ),
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="B" * 20_000,
            ) as base_prompt,
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
            self.assertLessEqual(len(prompt.encode("utf-8")), 24 * 1024)
            self.assertNotIn("__ARCHON_CONTROLLER_REPAIR_TASK_JSON__", prompt)
            self.assertIn("repair-0", prompt)
            self.assertNotIn("repair-19", prompt)

            base_prompt.return_value = "B" * (24 * 1024)
            with self.assertRaisesRegex(ValueError, "exceeds 24 KiB"):
                build_immediate_redraft_prompt(
                    project_name="project",
                    project_path=Path("/project"),
                    state_dir=Path("/project/.archon"),
                    iter_num=1,
                    target=Path("/project/Problem.lean"),
                    review_certificate=oversized_task,
                    debug_feedback=False,
                )


if __name__ == "__main__":
    unittest.main()
