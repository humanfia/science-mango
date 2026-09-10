from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

import archon.commands.loop.native_semantic_review as native_semantic_review

from archon.commands.loop.native_semantic_review import (
    BUNDLE_REL,
    build_native_schema_feedback,
    build_native_semantic_review_contract,
    render_independent_rederivation_instructions,
    validate_independent_rederivation,
)


class NativeSemanticReviewTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="native-semantic-review-")
        self.project = Path(self.temporary.name)
        state = self.project / ".archon"
        state.mkdir()
        (state / "config.json").write_text(
            json.dumps({
                "loop": {
                    "domain_profile": {
                        "name": "chemistry-native",
                        "lean_search_packages": ["Mathlib", "Physlib", "CRNT"],
                    }
                }
            }),
            encoding="utf-8",
        )
        self.target = self.project / "IChO2026Problems/problem_case_1.lean"
        self.target.parent.mkdir()
        self.target.write_text("theorem case_1 : True := by trivial\n", encoding="utf-8")
        self.row = self._row("case_1", outputs=2)
        self._write_bundle([self.row])

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def _row(record_id: str, *, outputs: int) -> dict[str, object]:
        requested = []
        for index in range(outputs):
            numeric = index == 0
            requested.append({
                "id": f"out_{index + 1}",
                "source_requirement": f"derive requested quantity {index + 1}",
                "kind": "numeric" if numeric else "classification",
                "unit": "mol" if numeric else "",
                "reporting_policy": (
                    {"kind": "significant_figures", "digits": 3}
                    if numeric else {"kind": "exact_symbolic"}
                ),
            })
        return {
            "schema_version": 1,
            "protocol": "icho-answer-blind-v1",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "id": record_id,
            "question": "Use the printed data to derive every requested quantity.",
            "current_question": "Derive the requested quantities.",
            "shared_context": "Treat printed constants as exact.",
            "previous_parts": [{"id": "prior", "question": "Prior source statement"}],
            "images": ["page.png"],
            "problem_assets": [{"kind": "problem_page", "path": "page.png"}],
            "requested_outputs": requested,
            "reporting_policy": {
                "intermediate_rounding": "forbidden",
                "final_precision": {
                    "kind": "per_requested_output",
                    "source": "requested_outputs",
                },
                "tie_rule": "half_away_from_zero",
            },
            "measurement_policy": {
                "stipulated_constants": "exact_as_printed",
            },
            "candidate_domain_policy": {
                "underdetermined_result": "must_be_reported",
            },
        }

    def _write_bundle(self, rows: list[dict[str, object]]) -> None:
        image_payload = b"problem-only image bytes"
        image_sha = hashlib.sha256(image_payload).hexdigest()
        image = self.project / "icho_2026_source/image/page.png"
        image.parent.mkdir(parents=True, exist_ok=True)
        image.write_bytes(image_payload)
        for row in rows:
            row["images"] = ["page.png"]
            row["problem_assets"] = [{
                "kind": "problem_page",
                "path": "page.png",
                "sha256": image_sha,
            }]
        path = self.project / BUNDLE_REL
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = "".join(
            json.dumps(row, ensure_ascii=False) + "\n" for row in rows
        ).encode("utf-8")
        path.write_bytes(payload)
        bundle_sha = hashlib.sha256(payload).hexdigest()
        (self.project / "isolation_manifest.json").write_text(
            json.dumps({
                "blind_bundle": {
                    "path": BUNDLE_REL.as_posix(),
                    "row_count": len(rows),
                    "sha256": bundle_sha,
                    "size": len(payload),
                },
                "blind_bundle_sha256": bundle_sha,
                "target_ids": sorted(str(row["id"]) for row in rows),
                "assets": {
                    "icho_2026_source/image/page.png": image_sha,
                },
            }),
            encoding="utf-8",
        )

    @staticmethod
    def _output_certificate(
        expected: dict[str, object],
        *,
        global_policy: dict[str, object],
        suffix: str,
    ) -> dict[str, object]:
        unit = str(expected["unit"])
        return {
            "id": expected["id"],
            "kind": expected["kind"],
            "source_requirement": expected["source_requirement"],
            "quantity_definition": "quantity named by the matching source request",
            "process_scope": {
                "kind": "overall",
                "description": "overall value across the process described in the source",
            },
            "basis": {
                "status": "not_applicable",
                "numerator": "not_applicable",
                "denominator": "not_applicable",
                "mass_or_composition_basis": "not_applicable",
            },
            "constants": [],
            "dependencies": [],
            "branch_conditions": [],
            "unit": unit,
            # This intentionally is not an official value. The gate checks the
            # source-derived evidence contract, not an answer key.
            "raw_result": {
                "value_or_expression": f"independent_expression_{suffix}",
                "exact_unrounded": True,
                "derivation": "substitute the printed inputs into the stated relation",
            },
            "reporting": {
                "policy": copy.deepcopy(expected["reporting_policy"]),
                "global_policy": copy.deepcopy(global_policy),
                "application": "apply the bundle policy once to the final raw result",
            },
            "lean_carriers": {
                "inputs": [f"NativeCase{suffix}.sourceInputs"],
                "relations": [f"NativeCase{suffix}.governingRelation"],
                "raw_result": [f"NativeCase{suffix}.rawResult"],
                "reported_result": [f"NativeCase{suffix}.reportedResult"],
            },
            "semantic_card_comparison": {
                "status": "matched",
                "evidence": "definition, scope, basis, unit, and raw carrier match",
            },
            "lean_statement_comparison": {
                "status": "matched",
                "evidence": "the Lean declarations encode the independently derived fields",
            },
            "source_locators": [{
                "kind": "problem_text",
                "reference": "current_question",
            }],
            "evidence": "source-first reconstruction agrees with both generated artifacts",
        }

    def _contract(self, target: Path | None = None) -> dict[str, object]:
        contract = build_native_semantic_review_contract(
            project_path=self.project,
            target=target or self.target,
        )
        self.assertIsInstance(contract, dict)
        assert isinstance(contract, dict)
        return contract

    def _review(self, contract: dict[str, object] | None = None) -> dict[str, object]:
        selected = contract or self._contract()
        outputs = selected["requested_outputs"]
        assert isinstance(outputs, list)
        global_policy = selected["reporting_policy"]
        assert isinstance(global_policy, dict)
        return {
            "independent_rederivation": {
                "schema_version": 1,
                "method": "source_first_without_lean",
                "ambiguity": "clear",
                "requested_outputs": [
                    self._output_certificate(
                        item,
                        global_policy=global_policy,
                        suffix=str(index + 1),
                    )
                    for index, item in enumerate(outputs)
                ],
            }
        }

    def test_complete_source_first_certificate_passes_without_answer_comparison(self) -> None:
        contract = self._contract()
        review = self._review(contract)
        review["independent_rederivation"]["requested_outputs"][0][
            "raw_result"
        ]["value_or_expression"] = "arbitrary_source_derived_symbolic_value"

        error, normalized = validate_independent_rederivation(review, contract)

        self.assertEqual(error, "")
        self.assertEqual(normalized, review["independent_rederivation"])
        self.assertEqual(
            [item["id"] for item in contract["requested_outputs"]],
            ["out_1", "out_2"],
        )

    def test_source_inventory_can_require_35_outputs(self) -> None:
        contract = self._contract()
        base = contract["requested_outputs"][0]
        contract["requested_outputs"] = [
            {**copy.deepcopy(base), "id": f"structure_{index}"}
            for index in range(35)
        ]
        review = self._review(contract)
        error, normalized = validate_independent_rederivation(review, contract)
        self.assertEqual(error, "")
        self.assertEqual(len(normalized["requested_outputs"]), 35)
        review["independent_rederivation"]["requested_outputs"].pop()
        error, _ = validate_independent_rederivation(review, contract)
        self.assertIn("exact ordered", error)

    @unittest.skipIf(os.geteuid() == 0, "tests unprivileged ownership")
    def test_user_owned_chmod_readonly_is_not_a_sealed_mount(self) -> None:
        path = self.project / "not-sealed"
        path.write_text("untrusted")
        path.chmod(0o444)
        self.assertFalse(native_semantic_review._read_only_user_mount(path))
        self.assertFalse(native_semantic_review._trusted_plain_file(path))

    def test_per_output_budget_uses_canonical_compact_json(self) -> None:
        contract = self._contract()
        review = self._review(contract)
        output = review["independent_rederivation"]["requested_outputs"][0]
        carriers = output["lean_carriers"]
        carriers["inputs"] = ["A.a"]

        def compact_size(value: object) -> int:
            return len(json.dumps(
                value,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8"))

        initial_size = compact_size(output)
        padding = native_semantic_review.MAX_OUTPUT_BYTES - initial_size
        self.assertGreater(padding, 0)
        carriers["inputs"] = ["A." + "a" * (padding + 1)]

        self.assertEqual(
            compact_size(output), native_semantic_review.MAX_OUTPUT_BYTES,
        )
        self.assertGreater(
            len(json.dumps(
                output, ensure_ascii=False, sort_keys=True,
            ).encode("utf-8")),
            native_semantic_review.MAX_OUTPUT_BYTES,
        )
        error, normalized = validate_independent_rederivation(review, contract)
        self.assertEqual(error, "")
        self.assertEqual(normalized, review["independent_rederivation"])

        carriers["inputs"][0] += "a"
        error, normalized = validate_independent_rederivation(review, contract)
        self.assertEqual(
            error,
            "independent_rederivation.requested_outputs[0] exceeds the compact Review certificate limit",
        )
        self.assertEqual(normalized, {})

    def test_prompt_example_parses_and_passes_the_same_validator(self) -> None:
        contract = self._contract()
        instructions = render_independent_rederivation_instructions(contract)
        self.assertIn("```json", instructions)
        match = re.search(r"```json\n(.*?)\n```", instructions, re.DOTALL)
        self.assertIsNotNone(match)
        parsed = json.loads(match.group(1))

        error, normalized = validate_independent_rederivation(parsed, contract)

        self.assertEqual(error, "")
        self.assertEqual(normalized, parsed["independent_rederivation"])

    def test_r10_schema_defects_are_strict_and_feedback_is_schema_only(self) -> None:
        contract = self._contract()
        missing_unit = self._review(contract)
        missing_unit["independent_rederivation"]["requested_outputs"][0][
            "constants"
        ] = [{
            "name": "source factor",
            "value": 1,
            "source_locator": {
                "kind": "problem_text",
                "reference": "shared_context",
            },
        }]

        unsupported_scope = self._review(contract)
        unsupported_scope["independent_rederivation"]["requested_outputs"][0][
            "process_scope"
        ]["kind"] = "OFFICIAL_ANSWER_SENTINEL"

        extra_role = self._review(contract)
        extra_role["independent_rederivation"]["requested_outputs"][0][
            "constants"
        ] = [{
            "name": "source factor",
            "value": 1,
            "unit": "dimensionless",
            "source_locator": {
                "kind": "problem_text",
                "reference": "shared_context",
            },
            "role": "PRIOR_DERIVATION_SENTINEL",
        }]

        cases = (
            (
                missing_unit,
                "missing unit",
                "independent_rederivation.requested_outputs[0].constants[0]",
                "required_exact_keys",
            ),
            (
                unsupported_scope,
                "process_scope.kind is unsupported",
                "independent_rederivation.requested_outputs[0].process_scope.kind",
                "allowed_values",
            ),
            (
                extra_role,
                "unexpected role",
                "independent_rederivation.requested_outputs[0].constants[0]",
                "required_exact_keys",
            ),
        )
        for review, expected_error, expected_path, contract_key in cases:
            with self.subTest(expected_error=expected_error):
                error, normalized = validate_independent_rederivation(review, contract)
                feedback = build_native_schema_feedback(error)

                self.assertIn(expected_error, error)
                self.assertEqual(normalized, {})
                self.assertIsInstance(feedback, dict)
                self.assertEqual(feedback["field_path"], expected_path)
                self.assertIn(contract_key, feedback)
                rendered = json.dumps(feedback, sort_keys=True)
                self.assertNotIn("OFFICIAL_ANSWER_SENTINEL", rendered)
                self.assertNotIn("PRIOR_DERIVATION_SENTINEL", rendered)

        semantic_mismatch = self._review(contract)
        semantic_mismatch["independent_rederivation"]["requested_outputs"][0][
            "unit"
        ] = "kg"
        semantic_error, _normalized = validate_independent_rederivation(
            semantic_mismatch, contract,
        )
        self.assertIn("does not exactly match", semantic_error)
        self.assertIsNone(build_native_schema_feedback(semantic_error))

        instructions = render_independent_rederivation_instructions(contract)
        for scope in (
            "cumulative", "instantaneous", "marginal", "not_applicable",
            "other", "overall", "per_cycle", "per_step", "repeated_process",
        ):
            self.assertIn(scope, instructions)
        self.assertIn(
            '"constants[]":["name","source_locator","unit","value"]',
            instructions,
        )
        self.assertIn(
            '"raw_result":["derivation","exact_unrounded",'
            '"value_or_expression"]',
            instructions,
        )
        self.assertIn("dependencies[].kind must be exactly one of", instructions)
        self.assertIn("schema_version must be the JSON integer 1", instructions)
        self.assertIn("unit=dimensionless", instructions)
        self.assertIn("field role is forbidden", instructions)
        self.assertIn("any other extra field", instructions)

    def test_blueprint_conflict_schema_feedback_is_full_and_schema_only(self):
        required_keys = [
            "blueprint_or_lean_claim",
            "evidence",
            "source_claim",
            "status",
        ]
        allowed_statuses = [
            "failed",
            "resolved_in_favor_of_problem_source",
            "unresolved",
        ]
        cases = (
            (
                "blueprint conflict 1 is not an object",
                "wrong_type",
                None,
            ),
            (
                "blueprint conflict 2 is missing source_claim",
                "missing_required_keys",
                "source_claim",
            ),
            (
                "blueprint conflict 3 is missing blueprint_or_lean_claim",
                "missing_required_keys",
                "blueprint_or_lean_claim",
            ),
            (
                "blueprint conflict 4 has invalid status",
                "unsupported_enum",
                None,
            ),
        )
        for error, issue, missing_key in cases:
            with self.subTest(error=error):
                feedback = build_native_schema_feedback(error)
                self.assertIsInstance(feedback, dict)
                self.assertEqual(feedback["issue"], issue)
                self.assertEqual(feedback["required_exact_keys"], required_keys)
                self.assertEqual(
                    feedback["enum_constraints"]["status"],
                    allowed_statuses,
                )
                if missing_key is None:
                    self.assertNotIn("missing_required_key", feedback)
                else:
                    self.assertEqual(
                        feedback["missing_required_key"], missing_key,
                    )

        list_feedback = build_native_schema_feedback(
            "blueprint_conflicts must be a list"
        )
        self.assertEqual(
            list_feedback["item_contract"]["required_exact_keys"],
            required_keys,
        )
        self.assertEqual(
            list_feedback["item_contract"]["enum_constraints"]["status"],
            allowed_statuses,
        )
        for unsafe_error in (
            "blueprint conflict 1 is missing EXPECTED_ANSWER_SENTINEL",
            "blueprint conflict 1000 is missing source_claim",
            "blueprint conflict 1 copies RAW_CLAIM_SENTINEL",
        ):
            self.assertIsNone(build_native_schema_feedback(unsafe_error))

    def test_feedback_registry_covers_all_controller_owned_nested_shapes(self) -> None:
        shape_cases = (
            ("independent_rederivation", "method"),
            ("independent_rederivation.requested_outputs[0]", "basis"),
            (
                "independent_rederivation.requested_outputs[0].process_scope",
                "description",
            ),
            ("independent_rederivation.requested_outputs[0].basis", "numerator"),
            (
                "independent_rederivation.requested_outputs[0].constants[0]",
                "unit",
            ),
            (
                "independent_rederivation.requested_outputs[0].dependencies[0]",
                "relation",
            ),
            (
                "independent_rederivation.requested_outputs[0].branch_conditions[0]",
                "condition",
            ),
            (
                "independent_rederivation.requested_outputs[0].raw_result",
                "derivation",
            ),
            (
                "independent_rederivation.requested_outputs[0].reporting",
                "application",
            ),
            (
                "independent_rederivation.requested_outputs[0].lean_carriers",
                "inputs",
            ),
            (
                "independent_rederivation.requested_outputs[0].semantic_card_comparison",
                "evidence",
            ),
            (
                "independent_rederivation.requested_outputs[0].lean_statement_comparison",
                "evidence",
            ),
            (
                "independent_rederivation.requested_outputs[0].constants[0].source_locator",
                "reference",
            ),
            (
                "independent_rederivation.requested_outputs[0].dependencies[0].source_locator",
                "reference",
            ),
            (
                "independent_rederivation.requested_outputs[0].branch_conditions[0].source_locator",
                "reference",
            ),
            (
                "independent_rederivation.requested_outputs[0].source_locators[0]",
                "reference",
            ),
        )
        for path, required_key in shape_cases:
            with self.subTest(path=path):
                feedback = build_native_schema_feedback(
                    f"{path} has invalid fields: missing {required_key}"
                )
                self.assertIsNotNone(feedback)
                assert feedback is not None
                self.assertEqual(feedback["field_path"], path)
                self.assertIn(required_key, feedback["required_exact_keys"])
                payload = json.dumps(
                    feedback,
                    ensure_ascii=True,
                    separators=(",", ":"),
                    sort_keys=True,
                )
                self.assertLessEqual(len(payload.encode("ascii")), 512)

        type_cases = (
            (
                "independent_rederivation.requested_outputs[0].basis",
                "object",
            ),
            (
                "independent_rederivation.requested_outputs[0].dependencies",
                "list",
            ),
            (
                "independent_rederivation.requested_outputs[0].dependencies[0].relation",
                "string",
            ),
            (
                "independent_rederivation.requested_outputs[0].id",
                "string",
            ),
            (
                "independent_rederivation.requested_outputs[0].kind",
                "string",
            ),
            (
                "independent_rederivation.requested_outputs[0].source_requirement",
                "string",
            ),
            (
                "independent_rederivation.requested_outputs[0].unit",
                "string",
            ),
        )
        for path, expected_type in type_cases:
            with self.subTest(path=path, expected_type=expected_type):
                article = "an" if expected_type == "object" else "a"
                feedback = build_native_schema_feedback(
                    f"{path} must be {article} {expected_type}"
                )
                self.assertIsNotNone(feedback)
                assert feedback is not None
                self.assertEqual(feedback["expected_type"], expected_type)

    def test_protocol_enum_feedback_is_fixed_and_semantic_errors_are_silent(self) -> None:
        contract = self._contract()
        enum_cases = (
            (
                "independent_rederivation.schema_version is unsupported",
                "independent_rederivation.schema_version",
                1,
            ),
            (
                "independent_rederivation.method must be source_first_without_lean",
                "independent_rederivation.method",
                "source_first_without_lean",
            ),
            (
                "independent_rederivation.requested_outputs[0].process_scope.kind is unsupported",
                "independent_rederivation.requested_outputs[0].process_scope.kind",
                "overall",
            ),
            (
                "independent_rederivation.requested_outputs[0].basis.status is unsupported",
                "independent_rederivation.requested_outputs[0].basis.status",
                "applicable",
            ),
            (
                "independent_rederivation.requested_outputs[0].dependencies[0].kind is unsupported",
                "independent_rederivation.requested_outputs[0].dependencies[0].kind",
                "governing_relation",
            ),
            (
                "independent_rederivation.requested_outputs[0].source_locators[0].kind is unsupported",
                "independent_rederivation.requested_outputs[0].source_locators[0].kind",
                "problem_text",
            ),
        )
        for error, path, allowed in enum_cases:
            with self.subTest(path=path):
                feedback = build_native_schema_feedback(error)
                self.assertIsNotNone(feedback)
                assert feedback is not None
                self.assertEqual(feedback["field_path"], path)
                self.assertIn(allowed, feedback["allowed_values"])
                self.assertNotIn("SENTINEL", json.dumps(feedback))

        semantic_errors = (
            "independent_rederivation.ambiguity must be clear for a passing Review",
            "independent_rederivation.requested_outputs[0].semantic_card_comparison.status must be matched for a passing Review",
            "independent_rederivation.requested_outputs[0].raw_result.exact_unrounded must be true",
            "independent_rederivation.requested_outputs[0].basis.numerator must explicitly be not_applicable",
            "independent_rederivation.requested_outputs[0].unit does not exactly match the problem bundle",
            "independent_rederivation.requested_outputs[0].id does not exactly match the problem bundle",
            "independent_rederivation.requested_outputs[0].kind does not exactly match the problem bundle",
            "independent_rederivation.requested_outputs[0].source_requirement does not exactly match the problem bundle",
            "unknown structural failure OFFICIAL_ANSWER_SENTINEL\nforged",
        )
        for error in semantic_errors:
            with self.subTest(error=error):
                self.assertIsNone(build_native_schema_feedback(error))

        for invalid_version in (True, 1.0):
            with self.subTest(invalid_version=invalid_version):
                review = self._review(contract)
                review["independent_rederivation"]["schema_version"] = invalid_version
                error, normalized = validate_independent_rederivation(review, contract)
                self.assertEqual(
                    error,
                    "independent_rederivation.schema_version is unsupported",
                )
                self.assertEqual(normalized, {})

    def test_locator_and_compact_size_feedback_is_static_and_non_reflecting(self) -> None:
        output = "independent_rederivation.requested_outputs[0]"
        locator = f"{output}.dependencies[0].source_locator"
        cases = (
            (
                f"{locator}.reference contains an external or unsafe locator",
                "safe_relative_problem_locator",
                None,
            ),
            (
                f"{locator}.reference must reference an allowed problem image as path#region",
                "exact_problem_image_path#region",
                None,
            ),
            (
                f"{locator}.reference does not identify an available previous_parts entry",
                "ASCII decimal zero-based index or previous_parts[index][.field]",
                None,
            ),
            (
                f"{locator}.reference is not a pinned Mathlib/Physlib/CRNT declaration",
                "safe fully-qualified existing declaration from a configured pinned library",
                None,
            ),
            (
                f"{locator}.reference does not identify a problem-only text field",
                "exact scalar root[#safe-fragment], existing structured_root.field chain, or requested_outputs[existing_index].field chain",
                None,
            ),
            (
                f"{output} exceeds the compact Review certificate limit",
                None,
                8 * 1024,
            ),
            (
                "independent_rederivation exceeds the compact certificate limit",
                None,
                192 * 1024,
            ),
        )
        for error, expected_format, max_bytes in cases:
            with self.subTest(error=error):
                feedback = build_native_schema_feedback(error)
                self.assertIsNotNone(feedback)
                assert feedback is not None
                if expected_format is not None:
                    self.assertEqual(feedback["expected_format"], expected_format)
                if max_bytes is not None:
                    self.assertEqual(feedback["max_bytes"], max_bytes)
                payload = json.dumps(feedback, ensure_ascii=True, sort_keys=True)
                self.assertLessEqual(len(payload.encode("ascii")), 512)
                self.assertNotIn("OFFICIAL_ANSWER_SENTINEL", payload)

        reflected_or_unknown = (
            f"{locator}.reference does not identify a problem-only text field\n"
            "OFFICIAL_ANSWER_SENTINEL",
            "independent_rederivation.requested_outputs[0].unit does not "
            "exactly match the problem bundle",
            "other.path does not identify an available previous_parts entry",
        )
        for error in reflected_or_unknown:
            with self.subTest(error=error):
                self.assertIsNone(build_native_schema_feedback(error))

        instructions = render_independent_rederivation_instructions(self._contract())
        self.assertIn("problem_text reference must be either", instructions)
        self.assertIn("requested_outputs[", instructions)
        self.assertIn("8192 UTF-8 bytes", instructions)
        self.assertIn("196608 UTF-8 bytes", instructions)

    def test_non_native_profiles_keep_the_historical_schema(self) -> None:
        config = self.project / ".archon/config.json"
        config.write_text(
            json.dumps({"loop": {"domain_profile": {"name": "physics"}}}),
            encoding="utf-8",
        )

        contract = build_native_semantic_review_contract(
            project_path=self.project,
            target=self.target,
        )
        error, normalized = validate_independent_rederivation({}, contract)

        self.assertIsNone(contract)
        self.assertEqual((error, normalized), ("", {}))

    def test_requested_outputs_must_have_exact_ordered_coverage(self) -> None:
        contract = self._contract()
        base = self._review(contract)
        mutations = {}
        missing = copy.deepcopy(base)
        missing["independent_rederivation"]["requested_outputs"].pop()
        mutations["missing"] = missing
        duplicate = copy.deepcopy(base)
        duplicate["independent_rederivation"]["requested_outputs"][1] = copy.deepcopy(
            duplicate["independent_rederivation"]["requested_outputs"][0]
        )
        mutations["duplicate"] = duplicate
        extra = copy.deepcopy(base)
        extra["independent_rederivation"]["requested_outputs"].append(copy.deepcopy(
            extra["independent_rederivation"]["requested_outputs"][0]
        ))
        mutations["extra"] = extra
        reordered = copy.deepcopy(base)
        reordered["independent_rederivation"]["requested_outputs"].reverse()
        mutations["reordered"] = reordered

        for name, review in mutations.items():
            with self.subTest(name=name):
                error, normalized = validate_independent_rederivation(review, contract)
                self.assertIn("exact ordered requested output ids", error)
                self.assertEqual(normalized, {})

    def test_method_ambiguity_fields_and_comparisons_fail_closed(self) -> None:
        contract = self._contract()
        mutations: list[tuple[str, dict[str, object], str]] = []
        wrong_method = self._review(contract)
        wrong_method["independent_rederivation"]["method"] = "artifact_first"
        mutations.append(("method", wrong_method, "source_first_without_lean"))
        ambiguous = self._review(contract)
        ambiguous["independent_rederivation"]["ambiguity"] = "needs_redraft"
        mutations.append(("ambiguity", ambiguous, "must be clear"))
        missing_basis = self._review(contract)
        del missing_basis["independent_rederivation"]["requested_outputs"][0]["basis"]
        mutations.append(("missing-field", missing_basis, "missing basis"))
        mismatch = self._review(contract)
        mismatch["independent_rederivation"]["requested_outputs"][0][
            "lean_statement_comparison"
        ]["status"] = "mismatched"
        mutations.append(("comparison", mismatch, "must be matched"))

        for name, review, expected_error in mutations:
            with self.subTest(name=name):
                error, normalized = validate_independent_rederivation(review, contract)
                self.assertIn(expected_error, error)
                self.assertEqual(normalized, {})

    def test_policy_and_unit_are_exactly_bound_to_problem_bundle(self) -> None:
        contract = self._contract()
        policy = self._review(contract)
        policy["independent_rederivation"]["requested_outputs"][0]["reporting"][
            "policy"
        ]["digits"] = 4
        unit = self._review(contract)
        unit["independent_rederivation"]["requested_outputs"][0]["unit"] = "kg"
        global_policy = self._review(contract)
        global_policy["independent_rederivation"]["requested_outputs"][0][
            "reporting"
        ]["global_policy"]["intermediate_rounding"] = "allowed"

        for name, review, expected in (
            ("output-policy", policy, "reporting.policy"),
            ("unit", unit, ".unit"),
            ("global-policy", global_policy, "reporting.global_policy"),
        ):
            with self.subTest(name=name):
                error, _ = validate_independent_rederivation(review, contract)
                self.assertIn(expected, error)

    def test_locators_accept_problem_only_inputs_and_reject_external_paths(self) -> None:
        contract = self._contract()
        allowed = self._review(contract)
        allowed["independent_rederivation"]["requested_outputs"][0][
            "source_locators"
        ] = [
            {"kind": "problem_text", "reference": "question#sentence-1"},
            {"kind": "problem_image", "reference": "page.png#table-1"},
            {"kind": "pinned_library", "reference": "Real.hasDerivAt_exp"},
        ]
        allowed["independent_rederivation"]["requested_outputs"][0][
            "dependencies"
        ] = [{
            "kind": "previous_part",
            "reference": "prior",
            "relation": "the prior question defines the dependency only",
            "source_locator": {
                "kind": "previous_parts",
                "reference": "previous_parts[0].question",
            },
        }]
        with mock.patch.object(
            native_semantic_review,
            "_verified_pinned_library_declarations",
            return_value=frozenset({"Real.hasDerivAt_exp"}),
        ):
            error, _ = validate_independent_rederivation(allowed, contract)
        self.assertEqual(error, "")

        unsafe_references = (
            ("problem_image", "https://example.invalid/answer.png#region"),
            ("problem_image", "../grader/answer.png#region"),
            ("problem_image", "page.png#"),
            ("problem_image", "page.png#region#two"),
            ("problem_image", "page.png#region/unsafe"),
            ("previous_parts", "previous_parts[7].answer"),
            ("pinned_library", "Project.Local.secret"),
        )
        for kind, reference in unsafe_references:
            with self.subTest(kind=kind, reference=reference), mock.patch.object(
                native_semantic_review,
                "_verified_pinned_library_declarations",
                return_value=frozenset(),
            ):
                review = self._review(contract)
                review["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{"kind": kind, "reference": reference}]
                error, normalized = validate_independent_rederivation(review, contract)
                self.assertTrue(error)
                self.assertEqual(normalized, {})

    def test_problem_image_bundle_prefix_is_a_canonicalized_alias(self) -> None:
        contract = self._contract()
        normalized_references = []
        for reference in (
            "page.png#table-1",
            "icho_2026_source/image/page.png#table-1",
        ):
            with self.subTest(reference=reference):
                review = self._review(contract)
                review["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{"kind": "problem_image", "reference": reference}]

                error, normalized = validate_independent_rederivation(review, contract)

                self.assertEqual(error, "")
                normalized_references.append(
                    normalized["requested_outputs"][0]["source_locators"][0][
                        "reference"
                    ]
                )

        self.assertEqual(normalized_references, ["page.png#table-1"] * 2)

    def test_problem_image_bundle_prefix_remains_exact_and_fail_closed(self) -> None:
        contract = self._contract()
        for reference in (
            "icho_2026_source/image/wrong.png#region",
            "other/image/page.png#region",
            "icho_2026_source/image/nested/page.png#region",
            "icho_2026_source/image/icho_2026_source/image/page.png#region",
            "icho_2026_source/image/../page.png#region",
            "/icho_2026_source/image/page.png#region",
        ):
            with self.subTest(reference=reference):
                review = self._review(contract)
                review["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{"kind": "problem_image", "reference": reference}]

                error, normalized = validate_independent_rederivation(review, contract)

                self.assertIn(".reference", error)
                self.assertEqual(normalized, {})

    def test_previous_parts_bare_decimal_is_range_checked_and_canonicalized(self) -> None:
        contract = self._contract()
        for reference, expected in (
            ("0", "previous_parts[0].question"),
            ("00", "previous_parts[0].question"),
            ("previous_parts[0]", "previous_parts[0].question"),
            ("previous_parts[0].question", "previous_parts[0].question"),
        ):
            with self.subTest(reference=reference):
                review = self._review(contract)
                review["independent_rederivation"]["requested_outputs"][0][
                    "dependencies"
                ] = [{
                    "kind": "previous_part",
                    "reference": "prior",
                    "relation": "depends on the prior question",
                    "source_locator": {
                        "kind": "previous_parts",
                        "reference": reference,
                    },
                }]

                error, normalized = validate_independent_rederivation(review, contract)

                self.assertEqual(error, "")
                self.assertEqual(
                    normalized["requested_outputs"][0]["dependencies"][0][
                        "source_locator"
                    ]["reference"],
                    expected,
                )

        for reference in (
            "-1",
            "1",
            "999999999999999999999999",
            "0;#eval",
            "previous_parts[-1]",
            "previous_parts[0]..question",
            "previous_parts[0].question/answer",
            "previous_parts[0].missing",
            "\u0660",
        ):
            with self.subTest(rejected=reference):
                review = self._review(contract)
                review["independent_rederivation"]["requested_outputs"][0][
                    "dependencies"
                ] = [{
                    "kind": "previous_part",
                    "reference": "prior",
                    "relation": "depends on the prior question",
                    "source_locator": {
                        "kind": "previous_parts",
                        "reference": reference,
                    },
                }]

                error, normalized = validate_independent_rederivation(review, contract)
                feedback = build_native_schema_feedback(error)

                self.assertTrue(error)
                self.assertEqual(normalized, {})
                self.assertIsNotNone(feedback)
                assert feedback is not None
                self.assertTrue(feedback["field_path"].endswith(".reference"))
                self.assertNotIn(reference, json.dumps(feedback, ensure_ascii=True))

        direct_conclusion = self._review(contract)
        direct_conclusion["independent_rederivation"]["requested_outputs"][0][
            "source_locators"
        ] = [{
            "kind": "previous_parts",
            "reference": "previous_parts[0].question",
        }]
        error, normalized = validate_independent_rederivation(
            direct_conclusion, contract,
        )
        self.assertIn("uncertified previous_parts conclusion", error)
        self.assertEqual(normalized, {})

    def test_certified_locator_is_bound_to_the_exact_producer_export(self) -> None:
        contract = self._contract()
        contract["certified_prior_result"] = {
            "context": {
                "producers": [{
                    "source_id": "icho_2026_t1_a4",
                    "typed_exports": [{
                        "export_id": (
                            "certified_prior_result:"
                            "icho_2026_t1_a4:metal_q_identity"
                        ),
                    }],
                }],
            },
        }
        review = self._review(contract)
        review["independent_rederivation"]["requested_outputs"][0][
            "source_locators"
        ] = [{
            "kind": "certified_prior_result",
            "reference": (
                "certified_prior_result.producers[0].typed_exports[0]"
            ),
        }]

        error, normalized = validate_independent_rederivation(review, contract)

        self.assertEqual(error, "")
        self.assertTrue(normalized)

        for reference in (
            "certified_prior_result.producers[1].typed_exports[0]",
            "certified_prior_result.producers[0].typed_exports[1]",
        ):
            with self.subTest(reference=reference):
                invalid = self._review(contract)
                invalid["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{
                    "kind": "certified_prior_result",
                    "reference": reference,
                }]
                error, normalized = validate_independent_rederivation(
                    invalid, contract,
                )
                self.assertIn("certified prior-result export", error)
                self.assertEqual(normalized, {})

        wrong_producer = copy.deepcopy(contract)
        wrong_producer["certified_prior_result"]["context"]["producers"][0][
            "typed_exports"
        ][0]["export_id"] = (
            "certified_prior_result:icho_2026_t1_a5:metal_q_identity"
        )
        error, normalized = validate_independent_rederivation(
            copy.deepcopy(review), wrong_producer,
        )
        self.assertIn("certified prior-result export", error)
        self.assertEqual(normalized, {})

    def test_problem_text_locator_resolves_exact_contract_fields(self) -> None:
        contract = self._contract()
        accepted = (
            "question",
            "question#sentence-1",
            "current_question#clause:2",
            "shared_context",
            "reporting_policy.intermediate_rounding",
            "reporting_policy.final_precision.kind",
            "measurement_policy.stipulated_constants",
            "candidate_domain_policy.underdetermined_result",
            "requested_outputs[0].id",
            "requested_outputs[0].reporting_policy.kind",
        )
        review = self._review(contract)
        review["independent_rederivation"]["requested_outputs"][0][
            "source_locators"
        ] = [
            {"kind": "problem_text", "reference": reference}
            for reference in accepted
        ]
        error, normalized = validate_independent_rederivation(review, contract)
        self.assertEqual(error, "")
        self.assertTrue(normalized)

        rejected = (
            "questionnaire",
            "question_evil",
            "question#",
            "question#fragment#two",
            "question#fragment/unsafe",
            "reporting_policy",
            "reporting_policy_evil",
            "reporting_policy.missing",
            "measurement_policy.missing",
            "candidate_domain_policy.missing",
            "requested_outputs[999].id",
            "requested_outputs[00].id",
            "requested_outputs[01].id",
            "requested_outputs[0]",
            "requested_outputs[0].missing",
            "requested_outputs[0].reporting_policy.missing",
            "requested_outputs[-1].id",
            "requested_outputs[0].id.trailing",
        )
        fixed_feedback_payloads: set[str] = set()
        for reference in rejected:
            with self.subTest(reference=reference):
                invalid = self._review(contract)
                invalid["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{"kind": "problem_text", "reference": reference}]
                error, normalized = validate_independent_rederivation(
                    invalid, contract,
                )
                feedback = build_native_schema_feedback(error)

                self.assertIn("problem-only text field", error)
                self.assertEqual(normalized, {})
                self.assertIsNotNone(feedback)
                assert feedback is not None
                self.assertTrue(feedback["field_path"].endswith(".reference"))
                fixed_feedback_payloads.add(
                    json.dumps(feedback, ensure_ascii=True, sort_keys=True)
                )
        self.assertEqual(len(fixed_feedback_payloads), 1)
        self.assertNotIn(
            "questionnaire", next(iter(fixed_feedback_payloads)),
        )

        for non_scalar in ({"forged": "text"}, ["forged"], None, "   "):
            with self.subTest(non_scalar=non_scalar):
                malformed_contract = copy.deepcopy(contract)
                malformed_contract["problem_evidence"]["question"] = non_scalar
                invalid = self._review(malformed_contract)
                invalid["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{"kind": "problem_text", "reference": "question"}]

                error, normalized = validate_independent_rederivation(
                    invalid, malformed_contract,
                )

                self.assertIn("problem-only text field", error)
                self.assertEqual(normalized, {})

    def test_pinned_locators_use_verified_origin_not_name_prefix(self) -> None:
        contract = self._contract()
        accepted = frozenset({
            "Real.hasDerivAt_exp",
            "DimArea.squareMeter",
            "CRNT.Reaction.vector",
        })
        review = self._review(contract)
        review["independent_rederivation"]["requested_outputs"][0][
            "source_locators"
        ] = [
            {"kind": "pinned_library", "reference": name}
            for name in sorted(accepted)
        ]
        with mock.patch.object(
            native_semantic_review,
            "_verified_pinned_library_declarations",
            return_value=accepted,
        ) as verify:
            error, normalized = validate_independent_rederivation(review, contract)

        self.assertEqual(error, "")
        self.assertTrue(normalized)
        self.assertEqual(verify.call_count, 1)
        self.assertEqual(
            verify.call_args.args[1], ("Mathlib", "Physlib", "CRNT"),
        )
        self.assertEqual(verify.call_args.args[2], set(accepted))

        rejected = (
            "Mathlib.DoesNotExist",
            "Project.Local.secret",
            "Real.hasDerivAt_exp;#eval",
            "Real.hasDerivAt_exp\n#check Nat",
            "MathlibEvil.Real.fake",
        )
        for reference in rejected:
            with self.subTest(reference=reference), mock.patch.object(
                native_semantic_review,
                "_verified_pinned_library_declarations",
                return_value=accepted,
            ):
                invalid = self._review(contract)
                invalid["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{"kind": "pinned_library", "reference": reference}]
                error, normalized = validate_independent_rederivation(
                    invalid, contract,
                )
                feedback = build_native_schema_feedback(error)

                self.assertIn("not a pinned", error)
                self.assertEqual(normalized, {})
                self.assertIsNotNone(feedback)
                assert feedback is not None
                self.assertTrue(feedback["field_path"].endswith(".reference"))
                self.assertNotIn(reference, json.dumps(feedback, ensure_ascii=True))

    def test_pinned_probe_has_a_fixed_distinct_declaration_limit(self) -> None:
        contract = self._contract()
        review = self._review(contract)
        too_many = {f"Library.Declaration{index}" for index in range(257)}
        with (
            mock.patch.object(
                native_semantic_review,
                "_pinned_references",
                return_value=too_many,
            ),
            mock.patch.object(
                native_semantic_review,
                "_verified_pinned_library_declarations",
            ) as probe,
        ):
            error, normalized = validate_independent_rederivation(review, contract)

        self.assertEqual(
            error,
            "independent_rederivation has too many distinct pinned library declarations",
        )
        self.assertEqual(normalized, {})
        probe.assert_not_called()
        self.assertEqual(build_native_schema_feedback(error)["max_items"], 256)

    @unittest.skipUnless(os.geteuid() == 0, "fixture requires genuine root-owned sealed artifacts")
    def test_pinned_origin_probe_is_external_bounded_and_artifact_bound(self) -> None:
        for relative, payload in (
            ("lakefile.toml", "name = \"native_test\"\n"),
            ("lake-manifest.json", '{"version":"1.2.0"}\n'),
            ("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
        ):
            (self.project / relative).write_text(payload, encoding="utf-8")
        packages_root = self.project / ".lake/packages"
        packages_root.mkdir(parents=True)
        lean_path = self.project / "lean-v4.31.0/bin/lean"
        lean_path.parent.mkdir(parents=True)
        lean_path.write_bytes(b"trusted Lean fixture")
        lean_path.chmod(0o755)
        artifacts = (
            ("mathlib", "Mathlib.Analysis.SpecialFunctions.ExpDeriv"),
            ("mathlib", "Mathlib.Generated"),
            ("Physlib", "Physlib.Units.WithDim.Area"),
            ("crnt-lean", "CRNT.Basic.Reaction"),
        )
        artifact_paths: dict[str, Path] = {}
        for package_dir, module in artifacts:
            artifact = (
                packages_root / package_dir / ".lake/build/lib/lean"
                / Path(*module.split("."))
            ).with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_bytes(b"sealed compiled module")
            artifact_paths[module] = artifact
        sources = (
            (
                "mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean",
                "namespace Real\ntheorem hasDerivAt_exp : True := by trivial\n"
                "theorem hasDerivAt_exp' : True := by trivial\n"
                "end Real\n",
            ),
            (
                "mathlib/Mathlib/Generated.lean",
                "@[to_additive Real.generatedDerivative]\n"
                "theorem Real.originalDerivative : True := by trivial\n",
            ),
            (
                "Physlib/Physlib/Units/WithDim/Area.lean",
                "namespace DimArea\ndef squareMeter : Nat := 1\nend DimArea\n",
            ),
            (
                "crnt-lean/CRNT/Basic/Reaction.lean",
                "namespace CRNT\nnamespace Reaction\ndef vector : Nat := 1\n"
                "end Reaction\nend CRNT\n",
            ),
        )
        for relative, source_text in sources:
            source = packages_root / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(source_text, encoding="utf-8")

        # A solver-owned project artifact with an allowed module name must not
        # enter the direct Lean search path at all.
        project_shadow = (
            self.project / ".lake/build/lib/lean/Mathlib/Analysis/"
            "SpecialFunctions/ExpDeriv.olean"
        )
        project_shadow.parent.mkdir(parents=True)
        project_shadow.write_bytes(b"solver shadow")

        references = {
            "Real.hasDerivAt_exp",
            "Real.hasDerivAt_exp'",
            "Real.generatedDerivative",
            "DimArea.squareMeter",
            "CRNT.Reaction.vector",
            "Mathlib.DoesNotExist",
            "Project.Local.secret",
            "Fake.prefixCollision",
        }
        explicit_output = "\n".join((
            "info: ARCHON_PINNED_ORIGIN|Real.hasDerivAt_exp|"
            "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
            "info: ARCHON_PINNED_ORIGIN|Real.hasDerivAt_exp'|"
            "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
            "info: ARCHON_PINNED_ORIGIN|DimArea.squareMeter|"
            "Physlib.Units.WithDim.Area",
            "info: ARCHON_PINNED_ORIGIN|CRNT.Reaction.vector|CRNT.Basic.Reaction",
            "info: ARCHON_PINNED_ORIGIN|Project.Local.secret|IChO.Local",
            "info: ARCHON_PINNED_ORIGIN|Fake.prefixCollision|MathlibEvil.Basic",
        ))
        fallback_output = (
            "info: ARCHON_PINNED_ORIGIN|Real.generatedDerivative|"
            "Mathlib.Generated"
        )
        version_completed = SimpleNamespace(
            returncode=0,
            stdout="Lean (version 4.31.0, x86_64, Release)\n",
            stderr="",
        )

        def run_probe(arguments, **kwargs):
            if arguments[1:] == ["--version"]:
                return version_completed
            probe_source = kwargs["input"]
            return SimpleNamespace(
                returncode=0,
                stdout=(
                    fallback_output
                    if "import Mathlib.Generated" in probe_source
                    else explicit_output
                ),
                stderr="",
            )

        native_semantic_review._pinned_source_tail_index.cache_clear()
        native_semantic_review._probe_pinned_library_declarations.cache_clear()

        with (
            mock.patch.object(
                native_semantic_review.shutil,
                "which",
                return_value=str(lean_path),
            ),
            mock.patch.object(
                native_semantic_review.subprocess,
                "run",
                side_effect=run_probe,
            ) as run,
        ):
            accepted = native_semantic_review._verified_pinned_library_declarations(
                self.project,
                ("Mathlib", "Physlib", "CRNT"),
                references,
            )
            accepted_cached = (
                native_semantic_review._verified_pinned_library_declarations(
                    self.project,
                    ("Mathlib", "Physlib", "CRNT"),
                    references,
                )
            )

            probe_calls = [
                call for call in run.call_args_list
                if "--stdin" in call.args[0]
            ]
            self.assertEqual(len(probe_calls), 2)
            source = probe_calls[0].kwargs["input"]
            self.assertIn(
                "import Mathlib.Analysis.SpecialFunctions.ExpDeriv", source,
            )
            self.assertIn("import Physlib.Units.WithDim.Area", source)
            self.assertIn("import CRNT.Basic.Reaction", source)
            self.assertNotIn("import IChO", source)
            self.assertIn("info.isUnsafe || info.isPartial", source)
            self.assertIn("import Mathlib.Generated", probe_calls[1].kwargs["input"])
            for call in probe_calls:
                self.assertEqual(
                    call.args[0],
                    [str(lean_path), "--stdin", "-M", "4096"],
                )
                self.assertEqual(call.kwargs["timeout"], 60)
                self.assertEqual(call.kwargs["cwd"], lean_path.parent)
                self.assertNotIn(
                    str(self.project / ".lake/build"),
                    call.kwargs["env"]["LEAN_PATH"],
                )
                self.assertNotIn("LEAN_SRC_PATH", call.kwargs["env"])
                self.assertNotIn("LEAN_SYSROOT", call.kwargs["env"])

        expected = frozenset({
            "Real.hasDerivAt_exp",
            "Real.hasDerivAt_exp'",
            "Real.generatedDerivative",
            "DimArea.squareMeter",
            "CRNT.Reaction.vector",
        })
        self.assertEqual(accepted, expected)
        self.assertEqual(accepted_cached, expected)

        # A cache hit must still re-check the exact defining artifact.
        artifact_paths[
            "Mathlib.Analysis.SpecialFunctions.ExpDeriv"
        ].chmod(0o666)
        def version_only(arguments, **_kwargs):
            if arguments[1:] == ["--version"]:
                return version_completed
            raise AssertionError("untrusted artifact must not be probed")

        with (
            mock.patch.object(
                native_semantic_review.shutil, "which", return_value=str(lean_path),
            ),
            mock.patch.object(
                native_semantic_review.subprocess, "run", side_effect=version_only,
            ),
        ):
            after_mode_drift = (
                native_semantic_review._verified_pinned_library_declarations(
                    self.project,
                    ("Mathlib", "Physlib", "CRNT"),
                    {"Real.hasDerivAt_exp"},
                )
            )
        self.assertNotIn("Real.hasDerivAt_exp", after_mode_drift)

        # Even a sealed transitive dependency may not shadow an allowed
        # defining module. Restore the allowed artifact, then add a duplicate.
        artifact_paths[
            "Mathlib.Analysis.SpecialFunctions.ExpDeriv"
        ].chmod(0o644)
        duplicate = (
            packages_root / "other-dependency/.lake/build/lib/lean/Mathlib/"
            "Analysis/SpecialFunctions/ExpDeriv.olean"
        )
        duplicate.parent.mkdir(parents=True)
        duplicate.write_bytes(b"cross-package shadow")
        with (
            mock.patch.object(
                native_semantic_review.shutil, "which", return_value=str(lean_path),
            ),
            mock.patch.object(
                native_semantic_review.subprocess, "run", side_effect=version_only,
            ),
        ):
            shadowed = native_semantic_review._verified_pinned_library_declarations(
                self.project,
                ("Mathlib", "Physlib", "CRNT"),
                {"Real.hasDerivAt_exp"},
            )
        self.assertEqual(shadowed, frozenset())

        native_semantic_review._pinned_source_tail_index.cache_clear()
        native_semantic_review._probe_pinned_library_declarations.cache_clear()

    def test_pinned_origin_probe_fails_closed_on_timeout_or_oversized_output(self) -> None:
        search_roots = (("mathlib", str(self.project)),)
        arguments = (
            "/usr/bin/true",
            ("Mathlib",),
            ("Real.hasDerivAt_exp",),
            ("Mathlib.Analysis.SpecialFunctions.ExpDeriv",),
            "f" * 64,
            "a" * 64,
            search_roots,
        )
        for result in (
            native_semantic_review.subprocess.TimeoutExpired("lean", 60),
            SimpleNamespace(
                returncode=0,
                stdout="X" * (64 * 1024 + 1),
                stderr="",
            ),
            SimpleNamespace(returncode=1, stdout="", stderr="RAW_DIAGNOSTIC"),
        ):
            success = SimpleNamespace(
                returncode=0,
                stdout=(
                    "ARCHON_PINNED_ORIGIN|Real.hasDerivAt_exp|"
                    "Mathlib.Analysis.SpecialFunctions.ExpDeriv"
                ),
                stderr="",
            )
            with self.subTest(result=type(result).__name__), mock.patch.object(
                native_semantic_review.subprocess,
                "run",
                side_effect=[result, success],
            ) as run:
                native_semantic_review._probe_pinned_library_declarations.cache_clear()
                with self.assertRaises(
                    native_semantic_review._PinnedResolutionUnavailable,
                ) as raised:
                    native_semantic_review._probe_pinned_library_declarations(
                        *arguments,
                    )
                origins = native_semantic_review._probe_pinned_library_declarations(
                    *arguments,
                )
                self.assertEqual(
                    origins,
                    ((
                        "Real.hasDerivAt_exp",
                        "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
                    ),),
                )
                self.assertEqual(run.call_count, 2)
                self.assertNotIn("RAW_DIAGNOSTIC", str(raised.exception))
        native_semantic_review._probe_pinned_library_declarations.cache_clear()

    @unittest.skipUnless(os.geteuid() == 0, "fixture requires genuine root-owned sealed sources")
    def test_pinned_source_index_retries_transient_read_and_covers_generated_names(
        self,
    ) -> None:
        packages_root = self.project / "sealed-packages"
        source = packages_root / "mathlib/Mathlib/Generated.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "namespace Real\n"
            "theorem derivative' : True := by trivial\n"
            "@[to_additive generatedDerivative]\n"
            "theorem originalDerivative : True := by trivial\n"
            "end Real\n",
            encoding="utf-8",
        )
        tails = ("derivative'", "generatedDerivative")
        native_semantic_review._pinned_source_tail_index.cache_clear()
        original_read_text = Path.read_text
        attempts = 0

        def flaky_read_text(path, *args, **kwargs):
            nonlocal attempts
            if path == source:
                attempts += 1
                if attempts == 1:
                    raise OSError("transient fixture failure")
            return original_read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", new=flaky_read_text):
            with self.assertRaises(
                native_semantic_review._PinnedResolutionUnavailable,
            ):
                native_semantic_review._pinned_source_tail_index(
                    str(packages_root), ("Mathlib",), tails, "f" * 64,
                )
            records = native_semantic_review._pinned_source_tail_index(
                str(packages_root), ("Mathlib",), tails, "f" * 64,
            )

        self.assertEqual(attempts, 2)
        self.assertIn(
            ("explicit", "Mathlib", "derivative'", "Mathlib.Generated"),
            records,
        )
        self.assertIn(
            (
                "fallback",
                "Mathlib",
                "generatedDerivative",
                "Mathlib.Generated",
            ),
            records,
        )
        native_semantic_review._pinned_source_tail_index.cache_clear()

    def test_invalid_or_duplicate_problem_bundle_fails_closed(self) -> None:
        self._write_bundle([self.row, copy.deepcopy(self.row)])

        contract = self._contract()
        error, normalized = validate_independent_rederivation({}, contract)

        self.assertFalse(contract["valid"])
        self.assertIn("duplicate id", contract["errors"][0])
        self.assertIn("contract is invalid", error)
        self.assertEqual(normalized, {})

    def test_bundle_manifest_and_problem_image_hashes_are_all_bound(self) -> None:
        clean = self._contract()
        self.assertTrue(clean["valid"])
        self.assertRegex(clean["bundle_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(clean["manifest_sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(clean["image_assets"][0]["path"], "page.png")
        self.assertEqual(
            clean["problem_evidence"]["measurement_policy"][
                "stipulated_constants"
            ],
            "exact_as_printed",
        )

        image = self.project / "icho_2026_source/image/page.png"
        image.write_bytes(b"tampered")
        tampered = self._contract()

        self.assertFalse(tampered["valid"])
        self.assertIn("hash does not match", tampered["errors"][0])

    def test_full32_48_output_certificate_stays_within_compact_budget(self) -> None:
        rows: list[dict[str, object]] = []
        for index in range(32):
            rows.append(self._row(f"scale_{index:02d}", outputs=2 if index < 16 else 1))
        self._write_bundle(rows)
        milestones: list[dict[str, object]] = []
        output_count = 0
        for index, row in enumerate(rows):
            target = self.project / f"IChO2026Problems/problem_{row['id']}.lean"
            target.write_text("theorem scale : True := by trivial\n", encoding="utf-8")
            contract = self._contract(target)
            review = self._review(contract)
            error, _ = validate_independent_rederivation(review, contract)
            self.assertEqual(error, "")
            outputs = review["independent_rederivation"]["requested_outputs"]
            output_count += len(outputs)
            milestones.append({
                "target": target.relative_to(self.project).as_posix(),
                "formalization_review": review,
            })
        payload = b"".join(
            (json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n").encode()
            for row in milestones
        )

        self.assertEqual(len(milestones), 32)
        self.assertEqual(output_count, 48)
        self.assertLess(len(payload), 128 * 1024)


if __name__ == "__main__":
    unittest.main()
