from __future__ import annotations

import copy
import hashlib
import json
import re
import tempfile
import unittest
from pathlib import Path

from archon.commands.loop.native_semantic_review import (
    BUNDLE_REL,
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
            {"kind": "previous_parts", "reference": "previous_parts[0].question"},
            {"kind": "pinned_library", "reference": "Mathlib.Data.Real.Basic"},
        ]
        error, _ = validate_independent_rederivation(allowed, contract)
        self.assertEqual(error, "")

        unsafe_references = (
            ("problem_image", "https://example.invalid/answer.png#region"),
            ("problem_image", "../grader/answer.png#region"),
            ("previous_parts", "previous_parts[7].answer"),
            ("pinned_library", "Project.Local.secret"),
        )
        for kind, reference in unsafe_references:
            with self.subTest(kind=kind, reference=reference):
                review = self._review(contract)
                review["independent_rederivation"]["requested_outputs"][0][
                    "source_locators"
                ] = [{"kind": kind, "reference": reference}]
                error, normalized = validate_independent_rederivation(review, contract)
                self.assertTrue(error)
                self.assertEqual(normalized, {})

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
