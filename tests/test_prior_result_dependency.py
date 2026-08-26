from __future__ import annotations

import copy
import importlib.util
import json
import os
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = (
    ROOT / "src" / "archon" / "commands" / "loop"
    / "prior_result_dependency.py"
)
SPEC = importlib.util.spec_from_file_location(
    "prior_result_dependency_minimal", MODULE_PATH
)
assert SPEC is not None and SPEC.loader is not None
PRIOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PRIOR)

A4 = "icho_2026_t1_a4"
A5 = "icho_2026_t1_a5"
A6 = "icho_2026_t1_a6"
OUTPUTS = {
    A4: (
        ("metal_q_identity", "classification", ""),
        ("hydrated_c_formula", "formula", ""),
        ("compound_d_formula", "formula", ""),
    ),
    A5: (
        ("compound_e_structure", "classification", ""),
        ("compound_f_structure", "classification", ""),
        ("compound_g_structure", "classification", ""),
    ),
}


class Fixture:
    def __init__(self) -> None:
        self.problem_pdf_sha256 = "a" * 64
        self.producer_bundle_sha256 = "b" * 64
        self.consumer_bundle_sha256 = "c" * 64
        self.shared_context = "shared chemistry context"
        self.bindings = PRIOR.build_validation_lineage_bindings(
            problem_id="icho_2026_t1",
            problem_pdf_sha256=self.problem_pdf_sha256,
            shared_context_sha256=PRIOR.canonical_prior_result_value_sha256(
                self.shared_context
            ),
            producer_bundle_sha256=self.producer_bundle_sha256,
            consumer_bundle_sha256=self.consumer_bundle_sha256,
            producer_inventory_sha256="d" * 64,
            consumer_inventory_sha256="e" * 64,
        )
        self.consumer = {
            "id": A6,
            "official_answer_seen": False,
            "problem_id": "icho_2026_t1",
            "shared_context": self.shared_context,
            "problem_assets": [{
                "kind": "problem_pdf",
                "sha256": self.problem_pdf_sha256,
            }],
            "previous_parts": [
                {"source_id": A4},
                {"source_id": A5},
            ],
        }
        self.snapshots = [
            self.snapshot(A4, range(1, 4)),
            self.snapshot(A5, range(1, 5)),
        ]

    def snapshot(self, source_id: str, prior_numbers) -> dict[str, object]:
        module = f"IChO2026Problems/problem_{source_id}.lean"
        module_sha256 = (
            "4" * 64 if source_id == A4 else "5" * 64
        )
        previous = [
            f"icho_2026_t1_a{number}" for number in prior_numbers
        ]
        exports = []
        for output_id, kind, unit in OUTPUTS[source_id]:
            payload = {
                "output_id": output_id,
                "kind": kind,
                "raw_value": f"value:{output_id}",
                "display_value": f"value:{output_id}",
                "unit": unit,
            }
            exports.append({
                "export_id": (
                    f"certified_prior_result:{source_id}:{output_id}"
                ),
                "result_payload": payload,
                "result_payload_sha256": (
                    PRIOR.canonical_prior_result_value_sha256(payload)
                ),
            })
        return {
            "schema_version": PRIOR.SCHEMA_VERSION,
            "controller_binding": self.bindings["producer"],
            "source_id": source_id,
            "source_record_sha256": (
                "6" * 64 if source_id == A4 else "7" * 64
            ),
            "previous_part_source_ids": previous,
            "previous_part_source_ids_sha256": (
                PRIOR.canonical_prior_result_value_sha256(previous)
            ),
            "source_bundle_sha256": self.producer_bundle_sha256,
            "answer_submission_sha256": (
                "8" * 64 if source_id == A4 else "9" * 64
            ),
            "official_answer_seen": False,
            "module": module,
            "module_sha256": module_sha256,
            "formalization_review": {"status": "passed"},
            "proof_review": {"status": "solved"},
            "compile_audit": {
                "status": "passed",
                "candidate_sha256": module_sha256,
                "returncode": 0,
                "sorry_count": 0,
            },
            "typed_exports": exports,
        }

    def build(self) -> dict[str, object]:
        return PRIOR.build_prior_result_dependency_context(
            consumer_target=(
                "IChO2026Problems/problem_icho_2026_t1_a6.lean"
            ),
            consumer_source_record=self.consumer,
            consumer_source_record_sha256=(
                PRIOR.canonical_prior_result_value_sha256(self.consumer)
            ),
            consumer_controller_binding=self.bindings["consumer"],
            producer_snapshots=self.snapshots,
        )


class PriorResultDependencyTest(unittest.TestCase):
    def test_normal_a4_a5_to_a6(self) -> None:
        fixture = Fixture()
        result = fixture.build()
        self.assertTrue(result)
        self.assertEqual(
            PRIOR.validate_prior_result_dependency_context_self(result), ""
        )
        self.assertEqual(
            [item["source_id"] for item in result["producers"]],
            [A4, A5],
        )
        self.assertEqual(
            sum(
                len(item["typed_exports"])
                for item in result["producers"]
            ),
            6,
        )
        self.assertNotIn("axiom_audit", result["producers"][0])
        self.assertEqual(
            set(result["producers"][0]["formalization_review"]),
            {"status"},
        )
        rendered = PRIOR.render_prior_result_dependency_prompt(result)
        self.assertIn(
            "certified_prior_result.producers[i].typed_exports[j]",
            rendered,
        )

    def test_review_status_compile_and_zero_sorry_rejected(self) -> None:
        mutations = (
            lambda fixture: fixture.snapshots[0][
                "formalization_review"
            ].update(status="retry"),
            lambda fixture: fixture.snapshots[1][
                "proof_review"
            ].update(status="retry"),
            lambda fixture: fixture.snapshots[0][
                "compile_audit"
            ].update(status="failed", returncode=1),
            lambda fixture: fixture.snapshots[1][
                "compile_audit"
            ].update(sorry_count=1),
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                fixture = Fixture()
                mutation(fixture)
                self.assertEqual(fixture.build(), {})

    def test_missing_and_duplicate_outputs_rejected(self) -> None:
        fixture = Fixture()
        fixture.snapshots[0]["typed_exports"].pop()
        self.assertEqual(fixture.build(), {})

        fixture = Fixture()
        duplicate = copy.deepcopy(
            fixture.snapshots[1]["typed_exports"][0]
        )
        fixture.snapshots[1]["typed_exports"][-1] = duplicate
        self.assertEqual(fixture.build(), {})

    def test_refusal_content_rejected(self) -> None:
        cases = (
            ("display_value", "证据不足，无法确定"),
            ("raw_value", {"status": "fail-closed"}),
            ("raw_value", None),
        )
        for field, value in cases:
            with self.subTest(field=field):
                fixture = Fixture()
                export = fixture.snapshots[0]["typed_exports"][0]
                export["result_payload"][field] = value
                export["result_payload_sha256"] = (
                    PRIOR.canonical_prior_result_value_sha256(
                        export["result_payload"]
                    )
                )
                self.assertEqual(fixture.build(), {})

    def test_tamper_and_stale_hashes_rejected(self) -> None:
        fixture = Fixture()
        result = fixture.build()

        tampered = copy.deepcopy(result)
        tampered["producers"][0]["typed_exports"][0][
            "result_payload"
        ]["display_value"] = "changed"
        self.assertIn(
            "payload hash",
            PRIOR.validate_prior_result_dependency_context_self(tampered),
        )

        tampered = copy.deepcopy(result)
        tampered["receipt_sha256"] = "0" * 64
        self.assertIn(
            "result hash",
            PRIOR.validate_prior_result_dependency_context_self(tampered),
        )

        changed_snapshots = copy.deepcopy(fixture.snapshots)
        changed_snapshots[0]["answer_submission_sha256"] = "0" * 64
        self.assertTrue(PRIOR.validate_prior_result_dependency_context(
            result,
            consumer_target=(
                "IChO2026Problems/problem_icho_2026_t1_a6.lean"
            ),
            consumer_source_record=fixture.consumer,
            consumer_source_record_sha256=(
                PRIOR.canonical_prior_result_value_sha256(
                    fixture.consumer
                )
            ),
            consumer_controller_binding=fixture.bindings["consumer"],
            producer_snapshots=changed_snapshots,
        ))

    def test_invalid_module_and_dependency_paths_rejected(self) -> None:
        fixture = Fixture()
        fixture.snapshots[0]["module"] = "../escape.lean"
        self.assertEqual(fixture.build(), {})

        with self.assertRaises(PRIOR.PriorResultDependencyError):
            PRIOR.prior_result_dependency_relative_path("../escape")

    def test_read_only_file_load_and_path_safety(self) -> None:
        fixture = Fixture()
        result = fixture.build()
        with tempfile.TemporaryDirectory(prefix="prior-result-load-") as raw:
            project = Path(raw)
            project.chmod(0o700)
            relative = PRIOR.prior_result_dependency_relative_path(A6)
            path = project / relative
            path.parent.mkdir(parents=True, mode=0o700)
            path.parent.chmod(0o700)
            path.write_text(
                json.dumps(
                    result, ensure_ascii=False, sort_keys=True,
                    separators=(",", ":"),
                )
                + "\n",
                encoding="utf-8",
            )
            path.chmod(0o444)
            loaded, reason = (
                PRIOR.load_prior_result_dependency_context_checked(
                    project, A6, controller_uid=os.geteuid()
                )
            )
            self.assertEqual(reason, "")
            self.assertEqual(loaded, result)

            path.chmod(0o644)
            loaded, reason = (
                PRIOR.load_prior_result_dependency_context_checked(
                    project, A6, controller_uid=os.geteuid()
                )
            )
            self.assertEqual(loaded, {})
            self.assertEqual(reason, "unsafe_receipt_file")


if __name__ == "__main__":
    unittest.main()
