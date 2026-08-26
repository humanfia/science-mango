from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import stat
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

SCRIPT = ROOT / "scripts" / "freeze_icho_a4_a5_prior_result.py"
SPEC = importlib.util.spec_from_file_location("freeze_icho_a4_a5", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
FREEZER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FREEZER)


def canonical(value: object) -> bytes:
    return (
        json.dumps(
            value, ensure_ascii=False, sort_keys=True,
            separators=(",", ":"), allow_nan=False,
        )
        + "\n"
    ).encode()


def sha(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


class Fixture:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.workspace = root / "run" / "workspace"
        self.producer_seed = root / "producer-seed"
        self.consumer_seed = root / "consumer-seed"
        for path in (self.workspace, self.producer_seed, self.consumer_seed):
            path.mkdir(parents=True, mode=0o700)
            path.chmod(0o700)

        self.pdf_sha = "c" * 64
        self.shared_context = "shared chemistry context"
        self.producer_rows = [
            self.row(
                FREEZER.A4,
                previous=[f"icho_2026_t1_a{index}" for index in range(1, 4)],
                requested=FREEZER.EXPECTED_OUTPUTS[FREEZER.A4],
            ),
            self.row(
                FREEZER.A5,
                previous=[f"icho_2026_t1_a{index}" for index in range(1, 5)],
                requested=FREEZER.EXPECTED_OUTPUTS[FREEZER.A5],
            ),
        ]
        self.consumer_rows = [
            self.row(FREEZER.A3, previous=[], requested=()),
            self.row(
                FREEZER.A6,
                previous=[FREEZER.A4, FREEZER.A5],
                requested=(),
            ),
        ]
        self.modules = {
            source_id: f"def {source_id}_result : Nat := 1\n".encode()
            for source_id in FREEZER.PRODUCER_IDS
        }
        self.answers = {
            source_id: {
                "schema_version": 1,
                "id": source_id,
                "official_answer_seen": False,
                "outputs": [
                    {
                        "id": output_id,
                        "kind": kind,
                        "raw_value": f"value:{output_id}",
                        "display_value": f"value:{output_id}",
                        "unit": unit,
                    }
                    for output_id, kind, unit
                    in FREEZER.EXPECTED_OUTPUTS[source_id]
                ],
            }
            for source_id in FREEZER.PRODUCER_IDS
        }
        self.formal = {"version": 1, "targets": {}}
        self.proof = {"version": 1, "targets": {}}
        for source_id in FREEZER.PRODUCER_IDS:
            target = FREEZER._target(source_id)
            module_sha = sha(self.modules[source_id])
            self.formal["targets"][target] = {
                "status": "passed",
                "candidate_sha256": module_sha,
            }
            self.proof["targets"][target] = {
                "status": "solved",
                "proof_review_route": "solved",
                "candidate_sha256": module_sha,
            }

    def row(self, source_id: str, *, previous, requested) -> dict[str, object]:
        return {
            "schema_version": 1,
            "id": source_id,
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "problem_id": "icho_2026_t1",
            "shared_context": self.shared_context,
            "problem_assets": [{
                "kind": "problem_pdf",
                "sha256": self.pdf_sha,
            }],
            "requested_outputs": [
                {"id": output_id, "kind": kind, "unit": unit}
                for output_id, kind, unit in requested
            ],
            "previous_parts": [
                {"source_id": item} for item in previous
            ],
        }

    def write_json(self, path: Path, value: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(canonical(value))

    def write_bundle(self, root: Path, rows: list[dict[str, object]]) -> None:
        bundle = b"".join(canonical(row) for row in rows)
        bundle_path = root / FREEZER.BUNDLE_REL
        bundle_path.parent.mkdir(parents=True, exist_ok=True)
        bundle_path.write_bytes(bundle)
        ids = [str(row["id"]) for row in rows]
        self.write_json(root / FREEZER.MANIFEST_REL, {
            "schema_version": 1,
            "protocol": "icho-problem-only-solver-seed-v1",
            "source_revision_disclosed": False,
            "target_ids": ids,
            "target_ids_sha256": FREEZER._value_sha256(ids),
            "blind_bundle_sha256": sha(bundle),
            "blind_bundle": {
                "path": FREEZER.BUNDLE_REL.as_posix(),
                "row_count": len(rows),
                "sha256": sha(bundle),
                "size": len(bundle),
            },
        })

    def persist(self) -> None:
        self.write_bundle(self.producer_seed, self.producer_rows)
        self.write_bundle(self.workspace, self.producer_rows)
        self.write_bundle(self.consumer_seed, self.consumer_rows)
        for source_id, payload in self.modules.items():
            path = self.workspace / FREEZER._target(source_id)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            self.write_json(
                self.workspace / FREEZER._answer_relative(
                    FREEZER._target(source_id)
                ),
                self.answers[source_id],
            )
        self.write_json(
            self.workspace / FREEZER.FORMAL_GATE_REL, self.formal
        )
        self.write_json(
            self.workspace / FREEZER.PROOF_GATE_REL, self.proof
        )

    def compile_checker(
        self, workspace: Path, target: str, candidate_sha256: str
    ) -> dict[str, object]:
        return {
            "schema_version": 1,
            "kind": "current_exact_source_compile_sorry_audit",
            "target": target,
            "candidate_sha256": candidate_sha256,
            "source_size": len((workspace / target).read_bytes()),
            "status": "passed",
            "compiles": True,
            "returncode": 0,
            "sorry_count": 0,
            "stdout_sha256": sha(b""),
            "stderr_sha256": sha(b""),
        }

    def build(self, *, checker=None):
        self.persist()
        return FREEZER.build_frozen_prior_result(
            producer_workspace=self.workspace,
            producer_seed=self.producer_seed,
            consumer_seed=self.consumer_seed,
            producer_inventory_sha256="a" * 64,
            consumer_inventory_sha256="b" * 64,
            current_compile_checker=checker or self.compile_checker,
            controller_uid=os.geteuid(),
        )


class FreezePriorResultTest(unittest.TestCase):
    def test_minimal_green_build_and_stage(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-minimal-") as raw:
            fixture = Fixture(Path(raw))
            receipt = fixture.build()
            self.assertEqual(
                FREEZER.validate_prior_result_dependency_context_self(receipt),
                "",
            )
            exports = [
                export
                for producer in receipt["producers"]
                for export in producer["typed_exports"]
            ]
            self.assertEqual(len(exports), 6)
            self.assertEqual(
                set(receipt["producers"][0]["formalization_review"]),
                {"status"},
            )
            self.assertNotIn("axiom_audit", receipt["producers"][0])
            output = Path(raw) / "staging" / "results.json"
            FREEZER.write_staged_receipt(
                output, receipt, controller_uid=os.geteuid()
            )
            self.assertEqual(stat.S_IMODE(output.stat().st_mode), 0o600)

    def test_reviewer_statuses_are_the_only_review_gate(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-review-") as raw:
            fixture = Fixture(Path(raw))
            target = FREEZER._target(FREEZER.A4)
            fixture.formal["targets"][target]["status"] = "retry"
            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError,
                "formalization semantic review",
            ):
                fixture.build()
        with tempfile.TemporaryDirectory(prefix="freezer-proof-") as raw:
            fixture = Fixture(Path(raw))
            target = FREEZER._target(FREEZER.A5)
            fixture.proof["targets"][target]["status"] = "retry"
            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError,
                "proof semantic review",
            ):
                fixture.build()

    def test_compile_and_zero_sorry_are_required(self) -> None:
        for field, value in (("returncode", 1), ("sorry_count", 1)):
            with self.subTest(field=field):
                with tempfile.TemporaryDirectory(
                    prefix="freezer-compile-"
                ) as raw:
                    fixture = Fixture(Path(raw))

                    def checker(workspace, target, candidate_sha256):
                        result = fixture.compile_checker(
                            workspace, target, candidate_sha256
                        )
                        result[field] = value
                        if field == "returncode":
                            result["status"] = "failed"
                            result["compiles"] = False
                        return result

                    with self.assertRaisesRegex(
                        FREEZER.FreezePriorResultError,
                        "compile/zero-sorry",
                    ):
                        fixture.build(checker=checker)

    def test_refusal_and_missing_values_are_rejected(self) -> None:
        cases = (
            ("raw_value", None),
            ("display_value", ""),
            ("display_value", "证据不足，无法确定"),
            ("raw_value", {"status": "fail-closed"}),
        )
        for field, value in cases:
            with self.subTest(field=field, value=value):
                with tempfile.TemporaryDirectory(
                    prefix="freezer-refusal-"
                ) as raw:
                    fixture = Fixture(Path(raw))
                    fixture.answers[FREEZER.A4]["outputs"][0][field] = value
                    with self.assertRaisesRegex(
                        FREEZER.FreezePriorResultError,
                        "concrete non-refusal",
                    ):
                        fixture.build()

    def test_structured_concrete_answer_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-structured-") as raw:
            fixture = Fixture(Path(raw))
            fixture.answers[FREEZER.A5]["outputs"][0]["raw_value"] = {
                "atoms": ["C", "H", "O"],
                "bonds": [[0, 1], [1, 2]],
            }
            receipt = fixture.build()
            self.assertEqual(
                FREEZER.validate_prior_result_dependency_context_self(receipt),
                "",
            )

    def test_cli_has_no_complex_trust_arguments(self) -> None:
        destinations = {
            action.dest for action in FREEZER._parser()._actions
        }
        forbidden = {
            "independent_review_receipt",
            "independent_review_run_id",
            "independent_reviewer_uid",
            "independent_source_first_inventory_sha256",
            "independent_clean_artifact_inventory_sha256",
            "environment_project",
            "verifier_uid",
            "verifier_gid",
            "controller_storage_uid",
            "solver_uid",
        }
        self.assertTrue(destinations.isdisjoint(forbidden))
        self.assertIn("lake_bin", destinations)


if __name__ == "__main__":
    unittest.main()
