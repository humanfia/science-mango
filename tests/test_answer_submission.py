from __future__ import annotations

import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = (
    ROOT / "src" / "archon" / "commands" / "loop"
    / "answer_submission.py"
)
SPEC = importlib.util.spec_from_file_location(
    "answer_submission_isolated", MODULE_PATH
)
assert SPEC is not None and SPEC.loader is not None
ANSWER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ANSWER)

AnswerSubmissionError = ANSWER.AnswerSubmissionError
answer_submission_path = ANSWER.answer_submission_path
answer_submission_relative_path = ANSWER.answer_submission_relative_path
freeze_answer_submissions = ANSWER.freeze_answer_submissions
validate_answer_submission = ANSWER.validate_answer_submission
validate_resolved_answer_submission = (
    ANSWER.validate_resolved_answer_submission
)


def _json_bytes(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


class AnswerSubmissionFreezeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.outside = self.root / "controller"
        (self.workspace / ".archon/task_results").mkdir(parents=True)
        (self.workspace / "IChO2026Problems").mkdir()
        (self.workspace / "icho_2026_source").mkdir()
        self.outside.mkdir()

        self.compile_patcher = mock.patch.object(
            ANSWER,
            "_run_current_lean_compile",
            side_effect=self._compile_result,
        )
        self.compile_check = self.compile_patcher.start()
        self.addCleanup(self.compile_patcher.stop)

        self.ids = ("icho_2026_t3_a1", "icho_2026_t9_a7")
        self.rows = (
            {
                "id": self.ids[0],
                "official_answer_seen": False,
                "requested_outputs": [
                    {
                        "id": "formula",
                        "kind": "formula",
                        "unit": "",
                        "reporting_policy": {"kind": "exact_symbolic"},
                    },
                    {
                        "id": "carbon_percent",
                        "kind": "numeric",
                        "unit": "%",
                        "reporting_policy": {
                            "kind": "decimal_places",
                            "digits": 2,
                        },
                    },
                ],
            },
            {
                "id": self.ids[1],
                "official_answer_seen": False,
                "requested_outputs": [
                    {
                        "id": "first_mz",
                        "kind": "integer",
                        "unit": "m/z",
                        "reporting_policy": {"kind": "exact_integer"},
                    },
                    {
                        "id": "second_mz",
                        "kind": "integer",
                        "unit": "m/z",
                        "reporting_policy": {"kind": "exact_integer"},
                    },
                ],
            },
        )
        self.bundle = self.workspace / "icho_2026_source/questions_only.jsonl"
        self.bundle.write_bytes(b"".join(_json_bytes(row) for row in self.rows))

        self.submissions = (
            {
                "schema_version": 1,
                "id": self.ids[0],
                "official_answer_seen": False,
                "outputs": [
                    {
                        "id": "formula",
                        "kind": "formula",
                        "raw_value": "C6H4BO2",
                        "display_value": "C6H4BO2",
                        "unit": "",
                    },
                    {
                        "id": "carbon_percent",
                        "kind": "numeric",
                        "raw_value": "7200/103",
                        "display_value": "69.90",
                        "unit": "%",
                    },
                ],
            },
            {
                "schema_version": 1,
                "id": self.ids[1],
                "official_answer_seen": False,
                "outputs": [
                    {
                        "id": "first_mz",
                        "kind": "integer",
                        "raw_value": 455,
                        "display_value": "455",
                        "unit": "m/z",
                    },
                    {
                        "id": "second_mz",
                        "kind": "integer",
                        "raw_value": 376,
                        "display_value": "376",
                        "unit": "m/z",
                    },
                ],
            },
        )
        self.lean_payloads: dict[str, bytes] = {}
        bundle_payload = self.bundle.read_bytes()
        bundle_sha256 = _sha256(bundle_payload)
        formal_targets: dict[str, object] = {}
        proof_targets: dict[str, object] = {}
        for target_id, row, submission in zip(
            self.ids, self.rows, self.submissions, strict=True
        ):
            submission_path = answer_submission_path(self.workspace, target_id)
            submission_path.write_text(
                json.dumps(submission, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
            target_rel = f"IChO2026Problems/problem_{target_id}.lean"
            lean = f"theorem problem_{target_id} : True := by trivial\n".encode()
            (self.workspace / target_rel).write_bytes(lean)
            self.lean_payloads[target_id] = lean
            digest = _sha256(lean)
            contract = {
                "schema_version": 1,
                "contract_kind": "native_problem_input_only",
                "authority": "problem-only",
                "evaluation_mode": "answer_blind",
                "target": target_rel,
                "source_bundle": "icho_2026_source/questions_only.jsonl",
                "source_bundle_sha256": bundle_sha256,
                "source_record_id": target_id,
                "source_record_sha256": _sha256(_json_bytes(row)),
                "answer_submission": answer_submission_relative_path(
                    target_id
                ).as_posix(),
                "answer_submission_sha256": _sha256(
                    submission_path.read_bytes()
                ),
                "candidate": target_rel,
                "candidate_sha256": digest,
            }
            formal_targets[target_rel] = {
                "status": "passed",
                "candidate_sha256": digest,
                "certificate": {"source_contract": contract},
            }
            proof_targets[target_rel] = {
                "status": "solved",
                "candidate_sha256": digest,
                "blind_review_certificate": {"source_contract": contract},
            }
        (self.workspace / ".archon/formalization-review-gate.json").write_text(
            json.dumps({"version": 2, "targets": formal_targets}), encoding="utf-8"
        )
        (self.workspace / ".archon/proof-review-gate.json").write_text(
            json.dumps({"version": 2, "targets": proof_targets}), encoding="utf-8"
        )

    def _compile_result(
        self,
        *,
        project_path: Path,
        target: Path,
        timeout_sec: int = 3600,
    ) -> dict[str, object]:
        del timeout_sec
        return {
            "file": target.resolve().relative_to(
                project_path.resolve()
            ).as_posix(),
            "status": "passed",
            "compiles": True,
            "returncode": 0,
            "sorry_count": 0,
        }

    def _gate(self, filename: str) -> tuple[Path, dict[str, object]]:
        path = self.workspace / ".archon" / filename
        return path, json.loads(path.read_text(encoding="utf-8"))

    def _write_gate(self, path: Path, gate: object) -> None:
        path.write_text(json.dumps(gate), encoding="utf-8")

    def test_path_helper_is_target_scoped_and_rejects_traversal(self) -> None:
        self.assertEqual(
            answer_submission_relative_path("icho_2026_t1_a6").as_posix(),
            ".archon/task_results/"
            "IChO2026Problems_problem_icho_2026_t1_a6.answer.json",
        )
        with self.assertRaises(AnswerSubmissionError):
            answer_submission_relative_path("../../official")

    def test_freeze_binds_rows_submissions_lean_and_gate_statuses(self) -> None:
        output = self.outside / "answer-freeze.json"
        receipt = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        payload = output.read_bytes()
        frozen = json.loads(payload)

        self.assertEqual(receipt["output_sha256"], _sha256(payload))
        self.assertEqual(receipt["target_count"], 2)
        self.assertEqual(
            receipt["counts"],
            {"valid": 2, "missing": 0, "invalid": 0, "certified": 2},
        )
        self.assertFalse(frozen["official_answer_seen"])
        self.assertEqual(frozen["target_ids"], list(self.ids))
        self.assertEqual(frozen["bundle"]["sha256"], _sha256(self.bundle.read_bytes()))
        for index, target_id in enumerate(self.ids):
            target = frozen["targets"][index]
            self.assertEqual(target["id"], target_id)
            self.assertEqual(
                target["blind_record_sha256"], _sha256(_json_bytes(self.rows[index]))
            )
            self.assertEqual(
                target["lean"]["sha256"], _sha256(self.lean_payloads[target_id])
            )
            self.assertEqual(target["submission"]["status"], "valid")
            self.assertEqual(target["lean"]["compile_status"], "passed")
            self.assertTrue(target["lean_certified"])
            self.assertEqual(
                target["gates"]["formalization_review"]["status"], "passed"
            )
            self.assertEqual(target["gates"]["proof_review"]["status"], "solved")
            self.assertTrue(
                target["gates"]["proof_review"]["candidate_matches_current_lean"]
            )
            self.assertEqual(
                target["gates"]["formalization_review"]["source_contract_status"],
                "bound",
            )
            self.assertEqual(
                target["gates"]["proof_review"]["source_contract_status"], "bound"
            )
            self.assertEqual(
                target["submission"]["value"]["outputs"],
                self.submissions[index]["outputs"],
            )


    def test_current_compile_failure_is_uncertified(self) -> None:
        self.compile_check.side_effect = lambda **kwargs: {
            "file": kwargs["target"].resolve().relative_to(
                kwargs["project_path"].resolve()
            ).as_posix(),
            "status": "failed",
            "compiles": False,
            "returncode": 1,
            "sorry_count": 0,
        }
        output = self.outside / "compile-failed-freeze.json"
        receipt = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        frozen = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(receipt["certified_count"], 0)
        self.assertTrue(all(
            target["lean"]["compile_status"] == "failed"
            and not target["lean_certified"]
            for target in frozen["targets"]
        ))

    def test_lean_mutation_during_compile_is_uncertified(self) -> None:
        changed = False

        def mutate(**kwargs: object) -> dict[str, object]:
            nonlocal changed
            target = kwargs["target"]
            project_path = kwargs["project_path"]
            assert isinstance(target, Path)
            assert isinstance(project_path, Path)
            result = self._compile_result(
                project_path=project_path, target=target,
            )
            if not changed:
                target.write_bytes(target.read_bytes() + b"-- changed\n")
                changed = True
            return result

        self.compile_check.side_effect = mutate
        output = self.outside / "lean-mutated-freeze.json"
        freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        frozen = json.loads(output.read_text(encoding="utf-8"))
        self.assertFalse(frozen["targets"][0]["lean_certified"])
        self.assertTrue(frozen["targets"][1]["lean_certified"])

    def test_invalid_submission_is_recorded_without_untrusted_content(self) -> None:
        submission_path = answer_submission_path(self.workspace, self.ids[0])
        secret = "DO_NOT_COPY_THIS_UNTRUSTED_VALUE"
        submission = self.submissions[0] | {"debug": secret}
        submission_path.write_text(json.dumps(submission), encoding="utf-8")
        output = self.outside / "freeze.json"
        receipt = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        frozen = json.loads(output.read_text(encoding="utf-8"))
        invalid = frozen["targets"][0]["submission"]

        self.assertEqual(receipt["invalid_count"], 1)
        self.assertEqual(receipt["valid_count"], 1)
        self.assertEqual(invalid["status"], "invalid")
        self.assertEqual(invalid["error_code"], "invalid_contract")
        self.assertEqual(
            set(invalid), {"status", "path", "file_sha256", "error_code"}
        )
        self.assertNotIn(secret, output.read_text(encoding="utf-8"))
        self.assertFalse(frozen["targets"][0]["lean_certified"])
        self.assertTrue(frozen["targets"][1]["lean_certified"])

    def test_nine_target_partial_freeze_keeps_fixed_denominator(self) -> None:
        extra_ids = tuple(f"icho_2026_placeholder_{index}" for index in range(7))
        extra_rows = tuple(
            {
                "id": target_id,
                "official_answer_seen": False,
                "requested_outputs": [
                    {
                        "id": "value",
                        "kind": "integer",
                        "unit": "",
                        "reporting_policy": {"kind": "exact_integer"},
                    }
                ],
            }
            for target_id in extra_ids
        )
        ids = self.ids + extra_ids
        rows = self.rows + extra_rows
        self.bundle.write_bytes(b"".join(_json_bytes(row) for row in rows))
        answer_submission_path(self.workspace, extra_ids[0]).write_bytes(
            b'{"schema_version":'
        )
        output = self.outside / "partial-freeze.json"
        receipt = freeze_answer_submissions(
            self.workspace, self.bundle, ids, output
        )
        frozen = json.loads(output.read_text(encoding="utf-8"))

        self.assertEqual(receipt["target_count"], 9)
        self.assertEqual(
            receipt["counts"],
            {"valid": 2, "missing": 6, "invalid": 1, "certified": 0},
        )
        self.assertEqual(len(frozen["targets"]), 9)
        self.assertEqual(
            [target["submission"]["status"] for target in frozen["targets"]],
            ["valid", "valid", "invalid"] + ["missing"] * 6,
        )
        self.assertEqual(
            set(frozen["targets"][2]["submission"]),
            {"status", "path", "file_sha256", "error_code"},
        )

    def test_submission_mutation_is_valid_but_unbound_and_uncertified(self) -> None:
        submission_path = answer_submission_path(self.workspace, self.ids[0])
        submission = json.loads(submission_path.read_text(encoding="utf-8"))
        submission["outputs"][0].update(
            {"raw_value": "C7H6O2", "display_value": "C7H6O2"}
        )
        submission_path.write_text(json.dumps(submission), encoding="utf-8")
        output = self.outside / "mutated-freeze.json"
        receipt = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        target = json.loads(output.read_text(encoding="utf-8"))["targets"][0]

        self.assertEqual(receipt["valid_count"], 2)
        self.assertEqual(receipt["certified_count"], 1)
        self.assertEqual(target["submission"]["status"], "valid")
        self.assertEqual(
            target["gates"]["formalization_review"]["source_contract_status"],
            "unbound",
        )
        self.assertEqual(
            target["gates"]["proof_review"]["source_contract_status"], "unbound"
        )
        self.assertFalse(target["lean_certified"])

    def test_formal_review_may_bind_an_older_lean_candidate(self) -> None:
        path, gate = self._gate("formalization-review-gate.json")
        target_rel = f"IChO2026Problems/problem_{self.ids[0]}.lean"
        old_sha256 = _sha256(b"older formally reviewed Lean body")
        record = gate["targets"][target_rel]
        record["candidate_sha256"] = old_sha256
        record["certificate"]["source_contract"]["candidate_sha256"] = old_sha256
        self._write_gate(path, gate)
        output = self.outside / "old-formal-freeze.json"
        freeze_answer_submissions(self.workspace, self.bundle, self.ids, output)
        target = json.loads(output.read_text(encoding="utf-8"))["targets"][0]

        formal = target["gates"]["formalization_review"]
        self.assertFalse(formal["candidate_matches_current_lean"])
        self.assertTrue(formal["candidate_matches_source_contract"])
        self.assertTrue(target["lean_certified"])

    def test_top_level_source_contract_location_is_accepted(self) -> None:
        path, gate = self._gate("proof-review-gate.json")
        target_rel = f"IChO2026Problems/problem_{self.ids[0]}.lean"
        record = gate["targets"][target_rel]
        contract = record.pop("blind_review_certificate")["source_contract"]
        record["source_contract"] = contract
        self._write_gate(path, gate)
        output = self.outside / "top-level-contract-freeze.json"
        freeze_answer_submissions(self.workspace, self.bundle, self.ids, output)
        target = json.loads(output.read_text(encoding="utf-8"))["targets"][0]

        self.assertEqual(
            target["gates"]["proof_review"]["source_contract_locations"],
            ["source_contract"],
        )
        self.assertTrue(target["lean_certified"])

    def test_mutated_review_answer_binding_fails_closed(self) -> None:
        path, gate = self._gate("proof-review-gate.json")
        target_rel = f"IChO2026Problems/problem_{self.ids[0]}.lean"
        record = gate["targets"][target_rel]
        record["blind_review_certificate"]["source_contract"][
            "answer_submission_sha256"
        ] = "0" * 64
        self._write_gate(path, gate)
        output = self.outside / "bad-binding-freeze.json"
        freeze_answer_submissions(self.workspace, self.bundle, self.ids, output)
        target = json.loads(output.read_text(encoding="utf-8"))["targets"][0]

        self.assertEqual(
            target["gates"]["proof_review"]["source_contract_status"], "unbound"
        )
        self.assertIsNone(
            target["gates"]["proof_review"]["answer_submission_sha256"]
        )
        self.assertFalse(target["lean_certified"])

    def test_missing_lean_and_malformed_gate_do_not_abort_freeze(self) -> None:
        (self.workspace / f"IChO2026Problems/problem_{self.ids[1]}.lean").unlink()
        proof_path, _ = self._gate("proof-review-gate.json")
        proof_path.write_bytes(b"{not-json")
        output = self.outside / "partial-artifacts-freeze.json"
        receipt = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        targets = json.loads(output.read_text(encoding="utf-8"))["targets"]

        self.assertEqual(receipt["valid_count"], 2)
        self.assertEqual(receipt["certified_count"], 0)
        self.assertEqual(
            targets[0]["gates"]["proof_review"]["status"], "malformed"
        )
        self.assertEqual(targets[1]["lean"]["status"], "missing")
        self.assertFalse(targets[0]["lean_certified"])
        self.assertFalse(targets[1]["lean_certified"])

    def test_freeze_is_create_once_idempotent_and_mode_0600(self) -> None:
        output = self.outside / "answer-freeze.json"
        first = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        original = output.read_bytes()
        second = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        self.assertEqual(first, second)
        self.assertEqual(output.stat().st_mode & 0o777, 0o600)

        submission_path = answer_submission_path(self.workspace, self.ids[0])
        submission = json.loads(submission_path.read_text(encoding="utf-8"))
        submission["outputs"][0].update(
            {"raw_value": "CH4", "display_value": "CH4"}
        )
        submission_path.write_text(json.dumps(submission), encoding="utf-8")
        with self.assertRaisesRegex(AnswerSubmissionError, "different contents"):
            freeze_answer_submissions(
                self.workspace, self.bundle, self.ids, output
            )
        self.assertEqual(output.read_bytes(), original)

    def test_closed_kind_policy_pairs_and_display_lexemes(self) -> None:
        normalized = validate_answer_submission(
            self.submissions[0], row=self.rows[0], target_id=self.ids[0]
        )
        self.assertEqual(normalized["outputs"][1]["raw_value"], "7200/103")

        bad_row = json.loads(json.dumps(self.rows[0]))
        bad_row["requested_outputs"][0]["reporting_policy"] = {
            "kind": "exact_integer"
        }
        with self.assertRaisesRegex(AnswerSubmissionError, "unsafe kind"):
            validate_answer_submission(
                self.submissions[0], row=bad_row, target_id=self.ids[0]
            )

        bad_integer = json.loads(json.dumps(self.submissions[1]))
        bad_integer["outputs"][0]["display_value"] = "455.0"
        with self.assertRaisesRegex(AnswerSubmissionError, "lexical integer"):
            validate_answer_submission(
                bad_integer, row=self.rows[1], target_id=self.ids[1]
            )

        for valid_display in ("7.03e12", "1.14E+3", "7.03 × 10^12"):
            valid_numeric = json.loads(json.dumps(self.submissions[0]))
            valid_numeric["outputs"][1]["display_value"] = valid_display
            with self.subTest(valid_display=valid_display):
                validate_answer_submission(
                    valid_numeric, row=self.rows[0], target_id=self.ids[0]
                )

        for invalid_display in (
            "7200/103", "NaN", "Infinity", "7.03 × 10¹²", 69.9,
        ):
            bad_numeric = json.loads(json.dumps(self.submissions[0]))
            bad_numeric["outputs"][1]["display_value"] = invalid_display
            with self.subTest(invalid_display=invalid_display):
                with self.assertRaises(AnswerSubmissionError):
                    validate_answer_submission(
                        bad_numeric, row=self.rows[0], target_id=self.ids[0]
                    )

    def test_resolved_validation_rejects_only_operational_nonanswers(self) -> None:
        for sentinel in (
            "blocked",
            "blocked_missing_rule",
            "blocked(missing rule)",
            "Blocked: missing rule",
            "Blocked. missing rule",
            "blocked-missing-rule",
            "blocked/missing-rule",
            "\u00a0blocked_missing_rule",
            "needs_redraft",
            "needs_redraft.",
            "needs\u00a0redraft",
            "needs‑redraft",
            "ＢＬＯＣＫＥＤ：missing rule",
            "failed_closed",
            "missing_source_closure",
            "review_exhausted",
            "retry_required",
            "not_started",
            "no_resolved_answer",
            "cannot_determine",
            "insufficient_evidence",
            "fail—closed",
            "fail_closed_missing_domain",
            "FAIL-CLOSED: missing domain",
            "fail/closed",
            "source_closure_failure",
            "source closure failure: missing manifest",
            "underdetermined",
            "underdetermined_missing_domain",
            "under-determined",
            "unknown",
            "unknown_candidate",
            "unresolved",
            "indeterminate",
        ):
            diagnostic = json.loads(json.dumps(self.submissions[0]))
            diagnostic["outputs"][0].update(
                {"raw_value": sentinel, "display_value": sentinel}
            )
            with self.subTest(sentinel=sentinel):
                self.assertEqual(
                    validate_answer_submission(
                        diagnostic, row=self.rows[0], target_id=self.ids[0]
                    )["outputs"][0]["raw_value"],
                    sentinel,
                )
                with self.assertRaisesRegex(
                    AnswerSubmissionError, "operational non-answer",
                ):
                    validate_resolved_answer_submission(
                        diagnostic, row=self.rows[0], target_id=self.ids[0]
                    )

        display_diagnostic = json.loads(json.dumps(self.submissions[0]))
        display_diagnostic["outputs"][0]["display_value"] = "needs-redraft: audit"
        self.assertEqual(
            validate_answer_submission(
                display_diagnostic, row=self.rows[0], target_id=self.ids[0]
            )["outputs"][0]["raw_value"],
            self.submissions[0]["outputs"][0]["raw_value"],
        )
        with self.assertRaisesRegex(AnswerSubmissionError, "operational non-answer"):
            validate_resolved_answer_submission(
                display_diagnostic, row=self.rows[0], target_id=self.ids[0]
            )

        for legitimate in (
            "unblocked", "blockade", "unknownium", "underdetermination",
        ):
            submission = json.loads(json.dumps(self.submissions[0]))
            submission["outputs"][0].update(
                {"raw_value": legitimate, "display_value": legitimate}
            )
            with self.subTest(legitimate=legitimate):
                normalized = validate_resolved_answer_submission(
                    submission, row=self.rows[0], target_id=self.ids[0]
                )
                self.assertEqual(
                    normalized["outputs"][0]["raw_value"], legitimate
                )

    def test_determination_status_requires_controller_contract(self) -> None:
        row = json.loads(json.dumps(self.rows[0]))
        row["requested_outputs"][0].update(
            {
                "kind": "classification",
                "resolution_expectation": "determination_status",
            }
        )
        submission = json.loads(json.dumps(self.submissions[0]))
        submission["outputs"][0].update(
            {
                "kind": "classification",
                "raw_value": "underdetermined",
                "display_value": "Underdetermined",
            }
        )
        normalized = validate_resolved_answer_submission(
            submission, row=row, target_id=self.ids[0],
        )
        self.assertEqual(
            normalized["outputs"][0]["raw_value"], "underdetermined",
        )

        submission["outputs"][0].update(
            {"raw_value": "fail_closed", "display_value": "fail closed"}
        )
        with self.assertRaisesRegex(
            AnswerSubmissionError, "operational non-answer",
        ):
            validate_resolved_answer_submission(
                submission, row=row, target_id=self.ids[0],
            )

        row["requested_outputs"][0]["resolution_expectation"] = "solver_choice"
        with self.assertRaisesRegex(
            AnswerSubmissionError, "resolution_expectation",
        ):
            validate_answer_submission(
                submission, row=row, target_id=self.ids[0],
            )

        row["requested_outputs"][0].update(
            {
                "kind": "formula",
                "resolution_expectation": "determination_status",
            }
        )
        submission["outputs"][0]["kind"] = "formula"
        with self.assertRaisesRegex(
            AnswerSubmissionError, "kind=classification",
        ):
            validate_answer_submission(
                submission, row=row, target_id=self.ids[0],
            )

    def test_freeze_rejects_operational_nonanswer_as_uncertified(self) -> None:
        submission_path = answer_submission_path(self.workspace, self.ids[0])
        submission = json.loads(submission_path.read_text(encoding="utf-8"))
        submission["outputs"][0].update(
            {
                "raw_value": "blocked_missing_rule",
                "display_value": "blocked_missing_rule",
            }
        )
        submission_path.write_text(json.dumps(submission), encoding="utf-8")

        output = self.outside / "operational-nonanswer-freeze.json"
        receipt = freeze_answer_submissions(
            self.workspace, self.bundle, self.ids, output
        )
        frozen = json.loads(output.read_text(encoding="utf-8"))

        self.assertEqual(receipt["invalid_count"], 1)
        self.assertEqual(receipt["certified_count"], 1)
        self.assertEqual(frozen["targets"][0]["submission"]["status"], "invalid")
        self.assertFalse(frozen["targets"][0]["lean_certified"])
        self.assertTrue(frozen["targets"][1]["lean_certified"])

    def test_bundle_output_contract_and_target_scope_mismatch_abort(self) -> None:
        unsafe_rows = json.loads(json.dumps(self.rows))
        unsafe_rows[0]["requested_outputs"][0]["reporting_policy"] = {
            "kind": "exact_integer"
        }
        self.bundle.write_bytes(
            b"".join(_json_bytes(row) for row in unsafe_rows)
        )
        with self.assertRaisesRegex(AnswerSubmissionError, "unsafe kind"):
            freeze_answer_submissions(
                self.workspace, self.bundle, self.ids, self.outside / "unsafe.json"
            )

        self.bundle.write_bytes(b"".join(_json_bytes(row) for row in self.rows))
        with self.assertRaisesRegex(AnswerSubmissionError, "ids/order"):
            freeze_answer_submissions(
                self.workspace,
                self.bundle,
                tuple(reversed(self.ids)),
                self.outside / "freeze.json",
            )

    def test_rejects_freeze_output_inside_workspace(self) -> None:
        with self.assertRaisesRegex(AnswerSubmissionError, "outside"):
            freeze_answer_submissions(
                self.workspace,
                self.bundle,
                self.ids,
                self.workspace / "answer-freeze.json",
            )


if __name__ == "__main__":
    unittest.main()
