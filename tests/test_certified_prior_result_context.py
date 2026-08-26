from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from archon.commands.loop.certified_prior_result_context import (
    CertifiedPriorResultContextError,
    canonical_value_sha256,
    load_certified_prior_result_context,
)
from archon.commands.loop.prior_result_dependency import (
    prior_result_dependency_relative_path,
)


class CertifiedPriorResultContextTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(
            prefix="certified-prior-result-"
        )
        self.project = Path(self.temporary.name)
        self.previous_parts = [
            {"source_id": "icho_2026_t1_a4", "question": "Identify Q."},
            {"source_id": "icho_2026_t1_a5", "question": "Identify E-G."},
        ]

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _load(self, consumer_record_id: str) -> dict[str, object]:
        return load_certified_prior_result_context(
            project_path=self.project,
            consumer_record_id=consumer_record_id,
            consumer_target_rel=(
                "IChO2026Problems/"
                f"problem_{consumer_record_id}.lean"
            ),
            source_bundle_sha256="a" * 64,
            source_record_sha256="b" * 64,
            previous_parts=self.previous_parts,
            trusted_controller_uid=os.geteuid(),
        )

    def _write_a6_context(self, *, file_mode: int = 0o444) -> Path:
        relative = prior_result_dependency_relative_path("icho_2026_t1_a6")
        path = self.project / relative
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps({"incomplete": True}) + "\n", encoding="utf-8")
        path.chmod(file_mode)
        return path

    def test_only_a6_requires_a_frozen_prior_result_context(self) -> None:
        self.assertEqual(self._load("icho_2026_t1_a3"), {})
        with self.assertRaisesRegex(
            CertifiedPriorResultContextError,
            "required certified prior-result context is missing",
        ):
            self._load("icho_2026_t1_a6")

    def test_nonconsumer_does_not_read_a_foreign_receipt_that_exists(
        self,
    ) -> None:
        receipt_path = self._write_a6_context()

        with mock.patch(
            "archon.commands.loop.certified_prior_result_context."
            "load_prior_result_dependency_context_checked",
            side_effect=AssertionError("foreign receipt must not be read"),
        ) as checked_loader:
            self.assertEqual(self._load("icho_2026_t1_a3"), {})

        checked_loader.assert_not_called()
        self.assertTrue(receipt_path.is_file())

    def test_a6_binds_the_final_core_producers_receipt_shape(self) -> None:
        receipt = {
            "consumer": {
                "source_id": "icho_2026_t1_a6",
                "target": (
                    "IChO2026Problems/problem_icho_2026_t1_a6.lean"
                ),
                "source_record_sha256": "b" * 64,
                "previous_parts_sha256": canonical_value_sha256(
                    self.previous_parts
                ),
                "source_bundle_sha256": "a" * 64,
                "official_answer_seen": False,
            },
            "producers": [
                {"source_id": "icho_2026_t1_a4", "typed_exports": []},
                {"source_id": "icho_2026_t1_a5", "typed_exports": []},
            ],
            "receipt_sha256": "c" * 64,
        }
        with mock.patch(
            "archon.commands.loop.certified_prior_result_context."
            "load_prior_result_dependency_context_checked",
            return_value=(receipt, ""),
        ) as checked_loader:
            binding = self._load("icho_2026_t1_a6")

        checked_loader.assert_called_once_with(
            self.project,
            "icho_2026_t1_a6",
            controller_uid=os.geteuid(),
        )
        self.assertEqual(binding["context"], receipt)
        self.assertEqual(binding["sha256"], "c" * 64)
        self.assertEqual(
            binding["path"],
            ".archon/prior-result-dependencies/icho_2026_t1_a6.json",
        )

    def test_a6_rejects_an_owner_writable_context_before_parsing(self) -> None:
        self._write_a6_context(file_mode=0o644)

        with self.assertRaisesRegex(
            CertifiedPriorResultContextError,
            "unsafe_receipt_file",
        ):
            self._load("icho_2026_t1_a6")

    def test_a6_rejects_a_solver_writable_context_directory(self) -> None:
        path = self._write_a6_context()
        path.parent.chmod(0o777)

        with self.assertRaisesRegex(
            CertifiedPriorResultContextError,
            "unsafe_receipt_directory",
        ):
            self._load("icho_2026_t1_a6")


if __name__ == "__main__":
    unittest.main()
