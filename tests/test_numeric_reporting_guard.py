from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from archon.commands.loop.numeric_reporting_guard import (
    NumericReportingGuardError,
    expected_reporting_quantum,
    finalized_guard_evidence,
    numeric_reporting_blockers,
    prepare_numeric_reporting_guard,
)
from archon.commands.loop.proof_review_gate import apply_proof_review
from archon.commands.loop.problem_only_review_contract import NUMERIC_REPORTING_MARKER_MISSING_REPAIR
from archon.commands.loop.review_preflight import check_review_target


GLOBAL_POLICY = {
    "intermediate_rounding": "forbidden",
    "tie_rule": "half_away_from_zero",
    "raw_result_required": True,
}


def _certificate(
    *,
    output_id: str = "numeric_result",
    kind: str = "significant_figures",
    digits: int | bool = 3,
    reported: str = "1.23e-40",
    quantum: str = "1e-42",
    raw: str = "Example.rawValue",
    declaration: str = "Example.reportingProof",
) -> str:
    return "-- archon:numeric-reporting-certificate " + json.dumps(
        {
            "schema_version": 1,
            "output_id": output_id,
            "reporting_policy_kind": kind,
            "reporting_policy_digits": digits,
            "reported_value": reported,
            "reporting_quantum": quantum,
            "raw_declaration": raw,
            "reporting_declaration": declaration,
        },
        separators=(",", ":"),
    )


class NumericReportingGuardTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.project = Path(self.temporary.name)
        (self.project / ".archon").mkdir()
        (self.project / ".archon/config.json").write_text(
            json.dumps({
                "loop": {"domain_profile": {"name": "chemistry-native"}},
            }),
            encoding="utf-8",
        )
        self.target = (
            self.project / "IChO2026Problems" / "problem_synthetic_case.lean"
        )
        self.target.parent.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def _write_problem(
        self,
        *,
        outputs: list[dict] | None = None,
        source: str | None = None,
    ) -> None:
        if outputs is None:
            outputs = [{
                "id": "numeric_result",
                "kind": "numeric",
                "unit": "synthetic-unit",
                "source_requirement": "calculate a synthetic result",
                "reporting_policy": {
                    "kind": "significant_figures",
                    "digits": 3,
                    "source": "uniform_test_policy",
                },
            }]
        row = {
            "id": "synthetic_case",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "requested_outputs": outputs,
            "reporting_policy": GLOBAL_POLICY,
        }
        payload = (json.dumps(row, sort_keys=True) + "\n").encode()
        bundle = self.project / "questions.jsonl"
        bundle.write_bytes(payload)
        (self.project / "isolation_manifest.json").write_text(
            json.dumps({
                "target_ids": ["synthetic_case"],
                "blind_bundle": {
                    "path": "questions.jsonl",
                    "sha256": hashlib.sha256(payload).hexdigest(),
                },
            }),
            encoding="utf-8",
        )
        if source is None:
            source = _certificate() + "\n"
        self.target.write_text(source, encoding="utf-8")

    def test_quantum_is_exact_for_arbitrary_magnitudes_and_places(self):
        cases = [
            ("significant_figures", 3, Fraction(123, 10**42), Fraction(1, 10**42)),
            ("significant_figures", 3, -Fraction(999 * 10**48), Fraction(10**48)),
            ("significant_figures", 1, Fraction(7, 10**900), Fraction(1, 10**900)),
            ("decimal_places", 0, Fraction(123), Fraction(1)),
            ("decimal_places", 100, Fraction(1), Fraction(1, 10**100)),
        ]
        for kind, digits, reported, expected in cases:
            with self.subTest(kind=kind, digits=digits, reported=reported):
                self.assertEqual(
                    expected_reporting_quantum(
                        kind=kind, digits=digits, reported_value=reported,
                    ),
                    expected,
                )

    def test_boolean_and_ambiguous_zero_are_rejected(self):
        with self.assertRaisesRegex(NumericReportingGuardError, "boolean"):
            expected_reporting_quantum(
                kind="decimal_places", digits=True, reported_value=Fraction(1),
            )
        with self.assertRaisesRegex(NumericReportingGuardError, "zero"):
            expected_reporting_quantum(
                kind="significant_figures", digits=3, reported_value=Fraction(0),
            )

    def test_ready_certificate_generates_exact_lean_proof_probe(self):
        self._write_problem()
        guard = prepare_numeric_reporting_guard(
            project_path=self.project, target=self.target,
        )
        self.assertEqual(guard.status, "ready")
        self.assertEqual(guard.numeric_outputs, 1)
        self.assertIn(
            "(_root_.Example.rawValue : ℝ)", guard.probe_suffix,
        )
        self.assertIn(
            "((123 : ℝ) / 1000000000000000000000000000000000000000000)",
            guard.probe_suffix,
        )
        self.assertIn("_root_.Example.reportingProof", guard.probe_suffix)
        passed = finalized_guard_evidence(guard, lean_probe_passed=True)
        self.assertEqual(passed["status"], "passed")

    def test_wrong_quantum_is_rejected_from_policy_and_magnitude(self):
        self._write_problem(source=_certificate(quantum="1e-40") + "\n")
        guard = prepare_numeric_reporting_guard(
            project_path=self.project, target=self.target,
        )
        self.assertEqual(guard.status, "failed")
        self.assertIn("must be 1/", guard.reason)

    def test_missing_duplicate_and_unsafe_certificates_fail_closed(self):
        sources = {
            "missing": "def Example.rawValue : ℝ := 1\n",
            "duplicate": _certificate() + "\n" + _certificate() + "\n",
            "unsafe": _certificate(raw="Example.rawValue; #eval 1") + "\n",
            "boolean": _certificate(digits=True) + "\n",
            "float-schema": _certificate().replace(
                '"schema_version":1', '"schema_version":1.0'
            ) + "\n",
        }
        for label, source in sources.items():
            with self.subTest(label=label):
                self._write_problem(source=source)
                guard = prepare_numeric_reporting_guard(
                    project_path=self.project, target=self.target,
                )
                self.assertEqual(guard.status, "failed")

    def test_every_numeric_output_requires_a_distinct_certificate(self):
        outputs = [
            {
                "id": output_id,
                "kind": "numeric",
                "reporting_policy": {
                    "kind": "decimal_places", "digits": 2, "source": "test",
                },
            }
            for output_id in ("first", "second")
        ]
        source = "\n".join([
            _certificate(
                output_id="first", kind="decimal_places", digits=2,
                reported="1.23", quantum="0.01",
            ),
            _certificate(
                output_id="second", kind="decimal_places", digits=2,
                reported="4.56", quantum="0.01",
                raw="Example.secondRaw",
                declaration="Example.secondReportingProof",
            ),
            "",
        ])
        self._write_problem(outputs=outputs, source=source)
        guard = prepare_numeric_reporting_guard(
            project_path=self.project, target=self.target,
        )
        self.assertEqual(guard.status, "ready")
        self.assertEqual(
            [item.output_id for item in guard.certificates], ["first", "second"],
        )

    def test_nonnumeric_target_is_not_applicable_and_rejects_extra_marker(self):
        outputs = [{
            "id": "formula",
            "kind": "formula",
            "reporting_policy": {"kind": "exact_symbolic", "source": "type"},
        }]
        self._write_problem(outputs=outputs, source="theorem x : True := by trivial\n")
        guard = prepare_numeric_reporting_guard(
            project_path=self.project, target=self.target,
        )
        self.assertEqual(guard.status, "not_applicable")

        self._write_problem(outputs=outputs, source=_certificate() + "\n")
        guard = prepare_numeric_reporting_guard(
            project_path=self.project, target=self.target,
        )
        self.assertEqual(guard.status, "failed")

    def test_non_native_profile_is_unchanged(self):
        (self.project / ".archon/config.json").write_text(
            json.dumps({"loop": {"domain_profile": {"name": "chemistry"}}}),
            encoding="utf-8",
        )
        self.target.write_text("theorem x : True := by trivial\n", encoding="utf-8")
        guard = prepare_numeric_reporting_guard(
            project_path=self.project, target=self.target,
        )
        self.assertFalse(guard.active)
        self.assertEqual(guard.status, "not_applicable")

    def test_malformed_explicit_native_profile_fails_closed(self):
        (self.project / ".archon/config.json").write_text(
            '{"loop":{"domain_profile":{"name":"chemistry-native"}',
            encoding="utf-8",
        )
        self.target.write_text("theorem x : True := by trivial\n", encoding="utf-8")
        guard = prepare_numeric_reporting_guard(
            project_path=self.project, target=self.target,
        )
        self.assertTrue(guard.active)
        self.assertEqual(guard.status, "failed")

    def test_preflight_compiles_source_plus_trusted_probe_in_one_pass(self):
        self._write_problem()
        calls: list[str] = []

        def fake_popen(command, **kwargs):
            probe = Path(command[-1])
            text = probe.read_text(encoding="utf-8")
            calls.append(text)
            self.assertIn("archon:numeric-reporting-certificate", text)
            self.assertIn("_root_.Example.reportingProof", text)
            return SimpleNamespace(
                pid=1234,
                returncode=0,
                communicate=Mock(return_value=("", "")),
            )

        with patch(
            "archon.commands.loop.review_preflight.subprocess.Popen",
            side_effect=fake_popen,
        ):
            result = check_review_target(
                project_path=self.project, target=self.target,
            )
        self.assertEqual(len(calls), 1)
        self.assertEqual(result["status"], "passed")
        self.assertTrue(result["compiles"])
        self.assertEqual(result["numeric_reporting"]["status"], "passed")

    def test_compiling_target_without_marker_gets_fixed_mechanical_route(self):
        self._write_problem(
            source="def Example.rawValue : ℝ := 1\n",
        )
        process = Mock()
        process.pid = 1234
        process.returncode = 0
        process.communicate.return_value = ("", "")

        with patch(
            "archon.commands.loop.review_preflight.subprocess.Popen",
            return_value=process,
        ):
            result = check_review_target(
                project_path=self.project, target=self.target,
            )

        self.assertEqual(result["status"], "failed")
        self.assertTrue(result["compiles"])
        self.assertEqual(result["returncode"], 0)
        reporting = result["numeric_reporting"]
        self.assertEqual(
            reporting["reason"], NUMERIC_REPORTING_MARKER_MISSING_REPAIR,
        )
        self.assertNotIn("lean_probe_passed", reporting)

    def test_failed_probe_with_compiling_original_keeps_compile_success(self):
        self._write_problem()
        calls: list[list[str]] = []

        def fake_popen(command, **kwargs):
            calls.append(command)
            probe_failed = Path(command[-1]).is_absolute()
            return SimpleNamespace(
                pid=1234,
                returncode=1 if probe_failed else 0,
                communicate=Mock(return_value=(
                    "probe rejected" if probe_failed else "original compiled",
                    "",
                )),
            )

        with patch(
            "archon.commands.loop.review_preflight.subprocess.Popen",
            side_effect=fake_popen,
        ):
            result = check_review_target(
                project_path=self.project, target=self.target,
            )

        self.assertEqual(len(calls), 2)
        self.assertEqual(
            calls[1][-1],
            "IChO2026Problems/problem_synthetic_case.lean",
        )
        self.assertEqual(result["status"], "failed")
        self.assertTrue(result["compiles"])
        self.assertEqual(result["returncode"], 0)
        self.assertEqual(result["diagnostics"], "original compiled")
        self.assertEqual(result["numeric_reporting"]["status"], "failed")
        self.assertFalse(result["numeric_reporting"]["lean_probe_passed"])
        self.assertNotEqual(
            result["numeric_reporting"]["reason"],
            NUMERIC_REPORTING_MARKER_MISSING_REPAIR,
        )

    def test_failed_guard_becomes_formalization_and_proof_blocker(self):
        preflight = {
            "targets": [{
                "file": "IChO2026Problems/problem_synthetic_case.lean",
                "numeric_reporting": {
                    "active": True,
                    "status": "failed",
                    "reason": "wrong quantum",
                },
            }],
        }
        blockers = numeric_reporting_blockers(preflight)
        self.assertEqual(len(blockers), 1)
        self.assertEqual(blockers[0]["source"], "numeric-reporting-guard")

        state = self.project / ".archon"
        session = state / "proof-journal/sessions/session_1"
        session.mkdir(parents=True)
        (session / "milestones.jsonl").write_text("", encoding="utf-8")
        self.target.write_text("theorem x : True := by trivial\n", encoding="utf-8")
        result = apply_proof_review(
            state_dir=state,
            project_path=self.project,
            session_dir=session,
            iter_num=1,
            reviewed_objectives=[self.target],
            max_iterations=3,
            deterministic_blockers={
                "IChO2026Problems/problem_synthetic_case.lean": "wrong quantum",
            },
        )
        self.assertEqual(
            result.needs_redraft,
            ("IChO2026Problems/problem_synthetic_case.lean",),
        )

    def test_unavailable_guard_blocks_and_retries_proof_without_redraft(self):
        rel = "IChO2026Problems/problem_synthetic_case.lean"
        blockers = numeric_reporting_blockers({
            "targets": [{
                "file": rel,
                "numeric_reporting": {
                    "active": True,
                    "status": "blocked",
                    "reason": "probe timed out",
                },
            }],
        })
        self.assertEqual(blockers[0]["kind"], "reporting_verification_unavailable")

        state = self.project / ".archon"
        session = state / "proof-journal/sessions/session_1"
        session.mkdir(parents=True)
        (session / "milestones.jsonl").write_text("", encoding="utf-8")
        self.target.write_text("theorem x : True := by trivial\n", encoding="utf-8")
        result = apply_proof_review(
            state_dir=state,
            project_path=self.project,
            session_dir=session,
            iter_num=1,
            reviewed_objectives=[self.target],
            max_iterations=3,
            deterministic_retry_blockers={rel: "probe timed out"},
        )
        self.assertEqual(result.retry, (rel,))
        self.assertEqual(result.needs_redraft, ())


if __name__ == "__main__":
    unittest.main()
