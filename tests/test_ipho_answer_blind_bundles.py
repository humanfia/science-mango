from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "build_ipho_answer_blind_bundles.py"
)
SPEC = importlib.util.spec_from_file_location("ipho_blind_builder", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IphoAnswerBlindBundleTests(unittest.TestCase):
    def _fixture(self, root: Path) -> dict[str, Path | list[dict]]:
        source_root = root / "ipho_source"
        raw_root = source_root / "raw"
        image_root = source_root / "image"
        raw_root.mkdir(parents=True)
        image_root.mkdir()
        (raw_root / "theory_general_instructions.pdf").write_bytes(
            b"problem-side constants and instructions"
        )
        for paper in MODULE.PAPER_ASSETS:
            (raw_root / f"{paper}_problem.pdf").write_bytes(
                f"problem-pdf-{paper}".encode()
            )
            (raw_root / f"{paper}_solution.pdf").write_bytes(
                f"sealed-controller-pdf-{paper}".encode()
            )
            (image_root / f"{paper}_page-1.png").write_bytes(
                f"question-page-{paper}".encode()
            )

        rows: list[dict] = []
        for position, (identifier, index, paper) in enumerate(
            MODULE.EXPECTED_TARGETS, 1
        ):
            rows.append(
                {
                    "id": identifier,
                    "index": index,
                    "source_index": f"source-{position}",
                    "problem_id": f"ipho_2026_{paper.lower()}",
                    "part_id": f"{paper}-part-{position}",
                    # This controller-side source header is deliberately dirty.
                    # The builder must ignore it and reconstruct question text.
                    "question": (
                        f"Controller source header: raw/{paper}_solution.pdf and "
                        f"raw/{paper}_marking_scheme.pdf"
                    ),
                    "shared_context": f"Problem-only physical context {position}.",
                    "current_question": f"Determine the requested quantity {position}.",
                    "answer": f"sealed-fixture-value-{position}",
                    "points": position / 10,
                    "marking": {"fixture": position},
                    "category": "IPhO 2026",
                    "dataset": "controller input",
                    "dataset_format": "native",
                    "paper": paper,
                    "kind": "experiment-derived" if paper == "E1" else "theory",
                    "formalization_ready": True,
                    "image": f"{paper}_page-1.png",
                    "images": [f"{paper}_page-1.png"],
                    "previous_parts": [],
                    "source_pdf": f"../ipho_2026_source/raw/{paper}_problem.pdf",
                    "solution_pdf": f"../ipho_2026_source/raw/{paper}_solution.pdf",
                    "source_page": 1,
                    "printed_page": position,
                    "source_url": "https://controller.invalid/problem",
                    "solution_url": "https://controller.invalid/sealed",
                }
            )
        rows[1]["previous_parts"] = [
            {
                "source_id": rows[0]["id"],
                "part_id": rows[0]["part_id"],
                "question": rows[0]["current_question"],
                "answer": "sealed-previous-value",
                "reusable_conclusions": ["sealed-derived-value"],
                "dependency_policy": "controller policy",
            }
        ]

        input_jsonl = root / "input.jsonl"
        input_jsonl.write_text(
            "".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8"
        )
        return {
            "source_root": source_root,
            "input": input_jsonl,
            "blind": root / "solver" / "questions.jsonl",
            "grader": root / "controller" / "grader.jsonl",
            "rows": rows,
        }

    @staticmethod
    def _read_jsonl(path: Path) -> list[dict]:
        return [
            json.loads(line)
            for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]

    def test_builds_exact_problem_only_and_controller_bundles(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            manifest = MODULE.build_bundles(
                input_jsonl=paths["input"],
                blind_output=paths["blind"],
                grader_output=paths["grader"],
                source_root=paths["source_root"],
            )
            blind_rows = self._read_jsonl(paths["blind"])
            grader_rows = self._read_jsonl(paths["grader"])

            self.assertEqual(len(blind_rows), 28)
            self.assertEqual(len(grader_rows), 28)
            self.assertEqual(
                [(row["id"], row["index"], row["paper"]) for row in blind_rows],
                list(MODULE.EXPECTED_TARGETS),
            )
            self.assertTrue(blind_rows[0]["question"].startswith("## Physical scenario"))
            self.assertNotIn("Controller source header", blind_rows[0]["question"])
            self.assertEqual(
                set(blind_rows[1]["previous_parts"][0]),
                {"source_id", "part_id", "question", "dependency_policy"},
            )
            self.assertEqual(
                blind_rows[1]["previous_parts"][0]["dependency_policy"],
                MODULE.DERIVE_POLICY,
            )
            for row in blind_rows:
                MODULE._assert_solver_safe(row)
                self.assertFalse(row["official_answer_seen"])
                self.assertEqual(row["problem_assets"][0]["kind"], "problem_pdf")
                self.assertEqual(
                    row["problem_assets"][0]["path"],
                    f"raw/{row['paper']}_problem.pdf",
                )
                self.assertTrue(
                    all(
                        asset["path"].startswith(
                            (
                                f"raw/{row['paper']}_",
                                f"image/{row['paper']}_",
                                "raw/theory_general_instructions.pdf",
                            )
                        )
                        for asset in row["problem_assets"]
                    )
                )
                if row["paper"] == "E1":
                    self.assertNotIn(
                        "problem_general_instructions",
                        {asset["kind"] for asset in row["problem_assets"]},
                    )
                else:
                    self.assertIn(
                        "problem_general_instructions",
                        {asset["kind"] for asset in row["problem_assets"]},
                    )

            blind_text = paths["blind"].read_text(encoding="utf-8")
            self.assertNotIn("sealed-fixture-value", blind_text)
            self.assertNotIn("sealed-previous-value", blind_text)
            self.assertNotIn("_solution.pdf", blind_text)
            self.assertNotIn("_marking_scheme.pdf", blind_text)
            self.assertNotIn("source_url", blind_text)

            self.assertEqual(
                grader_rows[0]["blind_record_sha256"],
                MODULE._sha256_bytes(MODULE._json_bytes(blind_rows[0])),
            )
            self.assertEqual(grader_rows[0]["official_points"], 0.1)
            self.assertEqual(grader_rows[0]["official_marking"], {"fixture": 1})
            self.assertEqual(manifest["row_count"], 28)

            blind_manifest = json.loads(
                MODULE._manifest_path(paths["blind"]).read_text(encoding="utf-8")
            )
            MODULE._assert_solver_safe(blind_manifest)
            self.assertNotIn("grader_output", blind_manifest)
            self.assertNotIn("solution_pdf_sha256", blind_manifest)
            self.assertEqual(blind_manifest["blind_sha256"], manifest["blind_sha256"])

    def test_recursive_solver_leak_is_rejected(self):
        for leaked in (
            {"nested": {"reasoning": "controller-only"}},
            {"nested": {"reusable_conclusions": []}},
            {"nested": {"grader_payload": {}}},
        ):
            with self.subTest(leaked=leaked):
                with self.assertRaisesRegex(ValueError, "forbidden solver key"):
                    MODULE._assert_solver_safe(leaked)

        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            rows = paths["rows"]
            rows[1]["previous_parts"][0]["question"] = "Read raw/T1_solution.pdf"
            paths["input"].write_text(
                "".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "controller asset"):
                MODULE.build_bundles(
                    input_jsonl=paths["input"],
                    blind_output=paths["blind"],
                    grader_output=paths["grader"],
                    source_root=paths["source_root"],
                )
            self.assertFalse(paths["blind"].exists())
            self.assertFalse(paths["grader"].exists())

    def test_wrong_count_and_order_fail_before_writing(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            rows = paths["rows"]
            paths["input"].write_text(
                "".join(json.dumps(row) + "\n" for row in rows[:-1]),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "expected exactly 28"):
                MODULE.build_bundles(
                    input_jsonl=paths["input"],
                    blind_output=paths["blind"],
                    grader_output=paths["grader"],
                    source_root=paths["source_root"],
                )
            self.assertFalse(paths["blind"].exists())

        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            rows = paths["rows"]
            rows[0]["formalization_ready"] = False
            paths["input"].write_text(
                "".join(json.dumps(row) + "\n" for row in rows),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                ValueError, "formalization_ready must be true"
            ):
                MODULE.build_bundles(
                    input_jsonl=paths["input"],
                    blind_output=paths["blind"],
                    grader_output=paths["grader"],
                    source_root=paths["source_root"],
                )
            self.assertFalse(paths["blind"].exists())

        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            rows = paths["rows"]
            rows[0], rows[1] = rows[1], rows[0]
            paths["input"].write_text(
                "".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "ordered inventory mismatch"):
                MODULE.build_bundles(
                    input_jsonl=paths["input"],
                    blind_output=paths["blind"],
                    grader_output=paths["grader"],
                    source_root=paths["source_root"],
                )
            self.assertFalse(paths["blind"].exists())

    def test_question_png_path_escape_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            rows = paths["rows"]
            (paths["source_root"] / "escape.png").write_bytes(b"outside image root")
            rows[0]["image"] = "../escape.png"
            rows[0]["images"] = ["../escape.png"]
            paths["input"].write_text(
                "".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "escapes image root"):
                MODULE.build_bundles(
                    input_jsonl=paths["input"],
                    blind_output=paths["blind"],
                    grader_output=paths["grader"],
                    source_root=paths["source_root"],
                )
            self.assertFalse(paths["blind"].exists())
            self.assertFalse(paths["grader"].exists())


if __name__ == "__main__":
    unittest.main()
