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
        self.source_images = [{
            "path": "icho_2026_source/image/problem-page.png",
            "sha256": "a" * 64,
        }]

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
            record_id="item_a2",
            problem_evidence=evidence,
            source_images=self.source_images,
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

    def test_source_image_component_chain_and_output_dependency(self) -> None:
        evidence = copy.deepcopy(self.evidence)
        evidence["requested_outputs"][0]["audit_requirements"] = [
            "image_component_accounting"
        ]
        evidence["requested_outputs"][1]["depends_on_output_ids"] = ["formula"]
        dag = build_semantic_dag(
            record_id="item_a2",
            problem_evidence=evidence,
            source_images=self.source_images,
        )
        nodes = {node["id"]: node for node in dag["nodes"]}
        self.assertEqual(
            nodes["source_image:0"],
            {
                "id": "source_image:0",
                "kind": "source_image",
                **self.source_images[0],
            },
        )
        for node_id, kind in (
            ("component_inventory:formula", "component_inventory"),
            ("connection_graph:formula", "connection_graph"),
            ("stoichiometric_balance:formula", "stoichiometric_balance"),
        ):
            self.assertEqual(nodes[node_id]["kind"], kind)
            self.assertEqual(nodes[node_id]["output_id"], "formula")

        edges = {
            (edge["from"], edge["to"], edge["kind"])
            for edge in dag["edges"]
        }
        self.assertTrue({
            (
                "source_image:0",
                "component_inventory:formula",
                "source_support",
            ),
            (
                "component_inventory:formula",
                "connection_graph:formula",
                "inventory_support",
            ),
            (
                "connection_graph:formula",
                "stoichiometric_balance:formula",
                "connection_support",
            ),
            (
                "stoichiometric_balance:formula",
                "derive:formula",
                "stoichiometric_support",
            ),
            ("derive:formula", "output:formula", "discharges"),
            ("output:formula", "derive:count", "output_dependency"),
            ("derive:count", "output:count", "discharges"),
        }.issubset(edges))
        self.assertNotIn(
            ("source_image:0", "derive:formula", "source_support"), edges,
        )
        self.assertEqual(
            nodes["output:count"]["depends_on_output_ids"], ["formula"],
        )
        kinds = semantic_dag_provenance(dag)["node_kind_counts"]
        self.assertEqual(kinds["source_image"], 1)
        self.assertEqual(kinds["component_inventory"], 1)
        self.assertEqual(kinds["connection_graph"], 1)
        self.assertEqual(kinds["stoichiometric_balance"], 1)

        prompt = render_solver_semantic_dag_prompt(
            dag, semantic_dag_provenance(dag),
        )
        for phrase in (
            "building-block identity and formula",
            "functional-group ports",
            "LCM/multiplicity",
            "eliminated small molecules",
            "unreduced whole-product formula or quantity",
            "GCD",
            "output_dependency",
        ):
            self.assertIn(phrase, prompt)

    def test_output_dependencies_fail_closed(self) -> None:
        variants: list[tuple[str, dict, str]] = []

        unknown = copy.deepcopy(self.evidence)
        unknown["requested_outputs"][1]["depends_on_output_ids"] = ["missing"]
        variants.append(("unknown", unknown, "unknown output id"))

        self_dependency = copy.deepcopy(self.evidence)
        self_dependency["requested_outputs"][1]["depends_on_output_ids"] = [
            "count"
        ]
        variants.append(("self", self_dependency, "self dependency"))

        forward = copy.deepcopy(self.evidence)
        forward["requested_outputs"][0]["depends_on_output_ids"] = ["count"]
        variants.append(("forward", forward, "only earlier"))

        cycle = copy.deepcopy(self.evidence)
        cycle["requested_outputs"][0]["depends_on_output_ids"] = ["count"]
        cycle["requested_outputs"][1]["depends_on_output_ids"] = ["formula"]
        variants.append(("cycle", cycle, "contains a cycle"))

        empty = copy.deepcopy(self.evidence)
        empty["requested_outputs"][1]["depends_on_output_ids"] = []
        variants.append(("empty", empty, "is invalid"))

        duplicate = copy.deepcopy(self.evidence)
        duplicate["requested_outputs"][1]["depends_on_output_ids"] = [
            "formula", " formula ",
        ]
        variants.append(("duplicate", duplicate, "is invalid"))

        for name, evidence, message in variants:
            with self.subTest(name=name):
                with self.assertRaisesRegex(SemanticDagError, message):
                    build_semantic_dag(
                        record_id="item_a2", problem_evidence=evidence,
                    )

    def test_source_images_are_strict_and_required_for_image_audit(self) -> None:
        evidence = copy.deepcopy(self.evidence)
        evidence["requested_outputs"][0]["audit_requirements"] = [
            "image_component_accounting"
        ]
        with self.assertRaisesRegex(
            SemanticDagError, "requires at least one source image",
        ):
            build_semantic_dag(
                record_id="item_a2", problem_evidence=evidence,
            )

        for name, images, message in (
            (
                "bad_digest",
                [{"path": "page.png", "sha256": "bad"}],
                "lowercase SHA-256",
            ),
            (
                "extra_field",
                [{
                    "path": "page.png",
                    "sha256": "a" * 64,
                    "value": "unbound",
                }],
                "exactly path and sha256",
            ),
            (
                "duplicate_path",
                [
                    {"path": "page.png", "sha256": "a" * 64},
                    {"path": "page.png", "sha256": "b" * 64},
                ],
                "duplicate path",
            ),
        ):
            with self.subTest(name=name):
                with self.assertRaisesRegex(SemanticDagError, message):
                    build_semantic_dag(
                        record_id="item_a2",
                        problem_evidence=self.evidence,
                        source_images=images,
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

    def test_provenance_rejects_malformed_graphs(self) -> None:
        base = self._dag()
        variants: list[tuple[str, dict, str]] = []

        duplicate_node = copy.deepcopy(base)
        duplicate_node["nodes"].append(
            copy.deepcopy(duplicate_node["nodes"][0])
        )
        variants.append(("duplicate_node", duplicate_node, "duplicate node id"))

        dangling = copy.deepcopy(base)
        dangling["edges"][0]["from"] = "missing:node"
        variants.append(("dangling", dangling, "dangling endpoint"))

        duplicate_edge = copy.deepcopy(base)
        duplicate_edge["edges"].append(
            copy.deepcopy(duplicate_edge["edges"][0])
        )
        variants.append(("duplicate_edge", duplicate_edge, "duplicate edge"))

        duplicate_pair = copy.deepcopy(base)
        same_pair = copy.deepcopy(duplicate_pair["edges"][0])
        same_pair["kind"] = "discharges"
        duplicate_pair["edges"].append(same_pair)
        variants.append(
            ("duplicate_pair", duplicate_pair, "duplicate directed edge")
        )

        self_edge = copy.deepcopy(base)
        self_edge["edges"][0]["to"] = self_edge["edges"][0]["from"]
        variants.append(("self_edge", self_edge, "self edge"))

        cycle = copy.deepcopy(base)
        cycle["edges"].append({
            "from": "output:formula",
            "to": "source:question",
            "kind": "output_dependency",
        })
        variants.append(("cycle", cycle, "directed cycle"))

        bad_edge_fields = copy.deepcopy(base)
        bad_edge_fields["edges"][0]["extra"] = "unbound"
        variants.append(("edge_fields", bad_edge_fields, "fields are invalid"))

        bad_edge_kind = copy.deepcopy(base)
        bad_edge_kind["edges"][0]["kind"] = "invented"
        variants.append(("edge_kind", bad_edge_kind, "kind is invalid"))

        duplicate_output = copy.deepcopy(base)
        output_count = next(
            node
            for node in duplicate_output["nodes"]
            if node["id"] == "output:count"
        )
        output_count["output_id"] = "formula"
        variants.append(
            ("duplicate_output", duplicate_output, "duplicate requested output")
        )

        extra_header = copy.deepcopy(base)
        extra_header["extra"] = "unbound"
        variants.append(("header", extra_header, "header fields are invalid"))

        for name, dag, message in variants:
            with self.subTest(name=name):
                with self.assertRaisesRegex(SemanticDagError, message):
                    semantic_dag_provenance(dag)

    def test_provenance_revalidates_source_image_nodes(self) -> None:
        base = build_semantic_dag(
            record_id="item_a2",
            problem_evidence=self.evidence,
            source_images=self.source_images,
        )
        mutated_digest = copy.deepcopy(base)
        source_image = next(
            node
            for node in mutated_digest["nodes"]
            if node["kind"] == "source_image"
        )
        source_image["sha256"] = "A" * 64
        with self.assertRaisesRegex(
            SemanticDagError, "source_image sha256 is invalid",
        ):
            semantic_dag_provenance(mutated_digest)

        extra_field = copy.deepcopy(base)
        source_image = next(
            node
            for node in extra_field["nodes"]
            if node["kind"] == "source_image"
        )
        source_image["extra"] = "unbound"
        with self.assertRaisesRegex(
            SemanticDagError, "source_image fields are invalid",
        ):
            semantic_dag_provenance(extra_field)

        duplicate_path = copy.deepcopy(base)
        duplicate_path["nodes"].append({
            "id": "source_image:1",
            "kind": "source_image",
            "path": self.source_images[0]["path"],
            "sha256": "b" * 64,
        })
        with self.assertRaisesRegex(
            SemanticDagError, "duplicate source_image path",
        ):
            semantic_dag_provenance(duplicate_path)

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


if __name__ == "__main__":
    unittest.main()
