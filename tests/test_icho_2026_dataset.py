"""Regression tests for IChO problem-page dependency closure."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "build_icho_2026_dataset.py"
)
SPEC = importlib.util.spec_from_file_location("icho_2026_dataset_builder", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class Icho2026DependencySourceImageTests(unittest.TestCase):
    def test_t5_a4_inherits_non_adjacent_fragment_page(self) -> None:
        by_part = {
            part["source_part_id"]: part
            for part in MODULE.build_parts()
        }

        self.assertEqual(
            by_part["T5-A4"]["images"],
            ["T5_page-3.png", "T5_page-2.png", "T5_page-1.png"],
        )

    def test_t1_a6_does_not_gain_unrelated_blue_elixir_page(self) -> None:
        by_part = {
            part["source_part_id"]: part
            for part in MODULE.build_parts()
        }

        self.assertEqual(
            by_part["T1-A6"]["images"],
            ["T1_page-4.png", "T1_page-3.png"],
        )

    def test_missing_dependency_fails_closed(self) -> None:
        parts = [{
            "source_part_id": "T1-A6",
            "paper": "T1",
            "subquestion": 6,
            "source_page": 9,
            "dependencies": ("T1-A5",),
            "images": ["T1_page-4.png", "T1_page-3.png"],
        }]

        with self.assertRaisesRegex(ValueError, "Missing source dependency: T1-A5"):
            MODULE.close_dependency_source_images(parts)

    def test_cyclic_dependency_fails_closed(self) -> None:
        parts = [
            {
                "source_part_id": part_id,
                "paper": "T1",
                "subquestion": subquestion,
                "source_page": 8,
                "dependencies": (dependency_id,),
                "images": ["T1_page-3.png", "T1_page-2.png"],
            }
            for part_id, subquestion, dependency_id in (
                ("T1-A4", 4, "T1-A5"),
                ("T1-A5", 5, "T1-A4"),
            )
        ]

        with self.assertRaisesRegex(ValueError, "Cyclic source dependency"):
            MODULE.close_dependency_source_images(parts)


if __name__ == "__main__":
    unittest.main()
