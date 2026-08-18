from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "build_icho_answer_blind_bundles.py"
)
SPEC = importlib.util.spec_from_file_location("icho_blind_builder", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IchoAnswerBlindBundleTests(unittest.TestCase):
    def _fixture(self, root: Path) -> dict[str, Path]:
        images = root / "images"
        images.mkdir()
        (images / "T4_page-3.png").write_bytes(b"problem image")
        problem_pdf = root / "theory_problem.pdf"
        solution_pdf = root / "theory_solution.pdf"
        problem_pdf.write_bytes(b"problem pdf")
        solution_pdf.write_bytes(b"solution pdf")
        input_jsonl = root / "input.jsonl"
        input_jsonl.write_text(
            json.dumps(
                {
                    "id": "icho_2026_t4_a8",
                    "index": "icho_2026_t4_a8",
                    "source_index": "T4-A8",
                    "problem_id": "icho_2026_t4",
                    "part_id": "T4-A8",
                    "current_question": "Calculate the daily energy.",
                    "shared_context": "Pressure, volume, R, and T are supplied.",
                    "answer": "7.04e12 J/day",
                    "answers": ["7.04e12 J/day"],
                    "marking": "2 points",
                    "solution_pdf": "theory_solution.pdf",
                    "solution_url": "https://example.test/solution",
                    "images": ["T4_page-3.png"],
                    "previous_parts": [
                        {
                            "source_id": "icho_2026_t4_a7",
                            "part_id": "T4-A7",
                            "question": "Calculate the enthalpy.",
                            "answer": "-781.9",
                            "reusable_conclusions": ["-781.876"],
                        }
                    ],
                    "source_pdf": "theory_problem.pdf",
                    "source_page": 39,
                    "printed_page": 3,
                    "source_url": "https://example.test/problem",
                    "category": "IChO 2026 Theory",
                    "points": 2,
                    "paper": "T4",
                    "kind": "theory",
                },
                ensure_ascii=False,
            )
            + "\n",
            encoding="utf-8",
        )
        return {
            "images": images,
            "problem_pdf": problem_pdf,
            "solution_pdf": solution_pdf,
            "input": input_jsonl,
            "blind": root / "blind.jsonl",
            "grader": root / "grader.jsonl",
        }

    def test_split_removes_answer_and_solution_material_recursively(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            manifest = MODULE.build_bundles(
                input_jsonl=paths["input"],
                blind_output=paths["blind"],
                grader_output=paths["grader"],
                image_root=paths["images"],
                problem_pdf=paths["problem_pdf"],
                solution_pdf=paths["solution_pdf"],
                expected_count=1,
            )
            blind_text = paths["blind"].read_text(encoding="utf-8")
            blind = json.loads(blind_text)
            grader = json.loads(paths["grader"].read_text(encoding="utf-8"))

            self.assertNotIn("7.04", blind_text)
            self.assertNotIn("781.9", blind_text)
            self.assertNotIn("theory_solution", blind_text)
            self.assertEqual(blind["evaluation_mode"], "answer_blind")
            self.assertFalse(blind["official_answer_seen"])
            self.assertEqual(
                blind["reporting_policy"]["final_precision"],
                {
                    "kind": "significant_figures",
                    "digits": 3,
                    "source": "uniform_blind_evaluation_default",
                },
            )
            self.assertEqual(
                blind["requested_outputs"],
                [
                    {
                        "id": "daily_energy",
                        "source_requirement": "total energy released per day",
                        "kind": "numeric",
                        "unit": "J day^-1",
                        "reporting_policy": {
                            "kind": "significant_figures",
                            "digits": 3,
                            "source": "uniform_blind_evaluation_default",
                        },
                    }
                ],
            )
            self.assertNotIn("source_url", blind)
            MODULE._assert_solver_safe(blind)
            self.assertEqual(
                set(blind["previous_parts"][0]),
                {"source_id", "part_id", "question", "dependency_policy"},
            )
            self.assertEqual(grader["official_answer"], "7.04e12 J/day")
            self.assertEqual(grader["blind_record_sha256"], MODULE._sha256_bytes(MODULE._json_bytes(blind)))
            self.assertEqual(manifest["row_count"], 1)
            solver_manifest = json.loads(
                paths["blind"].with_suffix(".jsonl.manifest.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertNotIn("grader_output", solver_manifest)
            self.assertNotIn("grader_sha256", solver_manifest)
            self.assertNotIn("solution_pdf_sha256", solver_manifest)
            self.assertFalse(solver_manifest["official_answer_seen"])

    def test_answer_page_image_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            (paths["images"] / "T4_answer_page-1.png").write_bytes(b"answer")
            row = json.loads(paths["input"].read_text(encoding="utf-8"))
            row["images"] = ["T4_answer_page-1.png"]
            paths["input"].write_text(json.dumps(row) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "forbidden"):
                MODULE.build_bundles(
                    input_jsonl=paths["input"],
                    blind_output=paths["blind"],
                    grader_output=paths["grader"],
                    image_root=paths["images"],
                    problem_pdf=paths["problem_pdf"],
                    solution_pdf=paths["solution_pdf"],
                    expected_count=1,
                )

    def test_wrong_inventory_count_fails_before_writing(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            with self.assertRaisesRegex(ValueError, "expected 32"):
                MODULE.build_bundles(
                    input_jsonl=paths["input"],
                    blind_output=paths["blind"],
                    grader_output=paths["grader"],
                    image_root=paths["images"],
                    problem_pdf=paths["problem_pdf"],
                    solution_pdf=paths["solution_pdf"],
                )
            self.assertFalse(paths["blind"].exists())
            self.assertFalse(paths["grader"].exists())

    def test_controller_target_scope_is_exact_ordered_and_fail_closed(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            first = json.loads(paths["input"].read_text(encoding="utf-8"))
            second = dict(first)
            second.update(
                {
                    "id": "icho_2026_t8_a6",
                    "index": "icho_2026_t8_a6",
                    "source_index": "T8-A6",
                    "problem_id": "icho_2026_t8",
                    "part_id": "T8-A6",
                    "current_question": "Calculate the quantum yield.",
                    "answer": "1.94 %",
                }
            )
            paths["input"].write_text(
                json.dumps(first) + "\n" + json.dumps(second) + "\n",
                encoding="utf-8",
            )

            manifest = MODULE.build_bundles(
                input_jsonl=paths["input"],
                blind_output=paths["blind"],
                grader_output=paths["grader"],
                image_root=paths["images"],
                problem_pdf=paths["problem_pdf"],
                solution_pdf=paths["solution_pdf"],
                expected_count=2,
                target_ids=["icho_2026_t8_a6", "icho_2026_t4_a8"],
            )
            rows = [
                json.loads(line)
                for line in paths["blind"].read_text(encoding="utf-8").splitlines()
            ]
            self.assertEqual(
                [row["id"] for row in rows],
                ["icho_2026_t8_a6", "icho_2026_t4_a8"],
            )
            self.assertEqual(manifest["row_count"], 2)
            self.assertEqual(
                manifest["ids"], ["icho_2026_t4_a8", "icho_2026_t8_a6"]
            )

            for requested, message in (
                (["icho_2026_t4_a8", "icho_2026_t4_a8"], "duplicates"),
                (["icho_2026_t9_a9"], "absent"),
                ([], "non-empty"),
            ):
                with self.subTest(requested=requested):
                    with self.assertRaisesRegex(ValueError, message):
                        MODULE.build_bundles(
                            input_jsonl=paths["input"],
                            blind_output=Path(raw) / f"bad-{message}.jsonl",
                            grader_output=Path(raw) / f"bad-{message}-grader.jsonl",
                            image_root=paths["images"],
                            problem_pdf=paths["problem_pdf"],
                            solution_pdf=paths["solution_pdf"],
                            expected_count=1,
                            target_ids=requested,
                        )

    def test_integrity_flag_cannot_claim_answer_seen(self):
        with self.assertRaisesRegex(ValueError, "integrity flag"):
            MODULE._assert_solver_safe({"official_answer_seen": True})

    def test_solution_reference_in_retained_text_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "solution asset"):
            MODULE._assert_solver_safe(
                {"current_question": "See assets/theory_solution.pdf"}
            )

    def test_multi_output_contract_has_per_output_reporting(self):
        outputs = MODULE.REQUESTED_OUTPUTS["icho_2026_t7_a3"]
        self.assertEqual([item["id"] for item in outputs], [
            "nitrogen_after_58_cycles", "cycles_for_97_percent",
        ])
        self.assertEqual(
            outputs[0]["reporting_policy"],
            {
                "kind": "decimal_places",
                "digits": 4,
                "source": "explicit_problem_instruction",
            },
        )
        self.assertEqual(
            outputs[1]["reporting_policy"],
            {"kind": "exact_integer", "source": "problem_output_type"},
        )

    def test_image_component_accounting_and_output_dependencies_are_opt_in(self):
        opted_in = {
            (target_id, output["id"])
            for target_id, outputs in MODULE.REQUESTED_OUTPUTS.items()
            for output in outputs
            if "audit_requirements" in output
        }
        self.assertEqual(
            opted_in,
            {
                ("icho_2026_t3_a1", "cof1_empirical_formula"),
                ("icho_2026_t9_a7", "first_fragment_mz"),
                ("icho_2026_t9_a7", "second_fragment_mz"),
            },
        )
        for target_id, output_id in opted_in:
            output = next(
                item
                for item in MODULE.REQUESTED_OUTPUTS[target_id]
                if item["id"] == output_id
            )
            self.assertEqual(
                output["audit_requirements"],
                ["image_component_accounting"],
            )

        t3_outputs = MODULE.REQUESTED_OUTPUTS["icho_2026_t3_a1"]
        self.assertNotIn("depends_on_output_ids", t3_outputs[0])
        self.assertEqual(
            t3_outputs[1]["depends_on_output_ids"],
            ["cof1_empirical_formula"],
        )
        self.assertNotIn("audit_requirements", t3_outputs[1])
        self.assertTrue(all(
            "depends_on_output_ids" not in output
            for output in MODULE.REQUESTED_OUTPUTS["icho_2026_t9_a7"]
        ))

    def test_requested_output_inventory_matches_real_theory_inventory(self):
        inventory = (
            Path(__file__).resolve().parents[1]
            / "icho_2026_run"
            / "references"
            / "icho_2026_theory_ready.jsonl"
        )
        ids = {
            json.loads(line)["id"]
            for line in inventory.read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
        self.assertEqual(set(MODULE.REQUESTED_OUTPUTS), ids)

    def test_problem_only_output_contract_corrections_are_pinned(self):
        stacking = MODULE.REQUESTED_OUTPUTS["icho_2026_t3_a6"]
        self.assertEqual(
            {item["unit"] for item in stacking},
            {"kJ mol^-1"},
        )
        self.assertTrue(
            all("between two layers of one repeat unit" in item["source_requirement"] for item in stacking)
        )

        # The problem and answer form pre-fill m/z 591 as the worked example;
        # only the remaining three peaks are requested from a blind solver.
        self.assertEqual(
            [item["id"] for item in MODULE.REQUESTED_OUTPUTS["icho_2026_t6_a4"]],
            ["ion_783", "ion_879", "ion_1174"],
        )

        explicit = {
            (target_id, output["id"], output["reporting_policy"]["digits"])
            for target_id, outputs in MODULE.REQUESTED_OUTPUTS.items()
            for output in outputs
            if output["reporting_policy"].get("source")
            == "explicit_problem_instruction"
        }
        self.assertEqual(
            explicit,
            {
                ("icho_2026_t3_a1", "cof1_carbon_mass_percent", 2),
                ("icho_2026_t7_a3", "nitrogen_after_58_cycles", 4),
            },
        )
        for target_id in ("icho_2026_t4_a8", "icho_2026_t8_a6"):
            self.assertEqual(
                MODULE.REQUESTED_OUTPUTS[target_id][0]["reporting_policy"]["source"],
                "uniform_blind_evaluation_default",
            )


if __name__ == "__main__":
    unittest.main()
