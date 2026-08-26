from __future__ import annotations

import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest import mock

import archon.commands.loop.parallel_formalization_review as review
from archon.commands.loop.parallel_review import TargetReviewSpec


class FormalizationResolvedAnswerGateTest(unittest.TestCase):
    def _run_worker(
        self,
        *,
        root: Path,
        milestone: dict,
        resolution_error: str,
    ):
        output_dir = root / "review"
        spec = TargetReviewSpec(
            rel="Problems/problem_a.lean",
            prompt="bounded review prompt",
            output_dir=str(output_dir),
            log_base=str(output_dir / "agent"),
            attempt=1,
            source_contract={"contract_kind": "native-test-contract"},
        )
        runner = mock.Mock()
        runner.run.return_value = True
        resolved_validator = mock.Mock(
            return_value=(None, resolution_error),
        )
        with ExitStack() as patches:
            patches.enter_context(mock.patch.object(
                review,
                "validate_review_source_contract_current",
                return_value="",
            ))
            patches.enter_context(mock.patch.object(
                review, "native_problem_image_args", return_value=[],
            ))
            patches.enter_context(mock.patch.object(
                review, "build_runner", return_value=runner,
            ))
            patches.enter_context(mock.patch.object(
                review,
                "materialize_controller_review_provenance",
                return_value="",
            ))
            patches.enter_context(mock.patch.object(
                review,
                "build_native_semantic_review_contract",
                return_value=None,
            ))
            patches.enter_context(mock.patch.object(
                review,
                "load_target_formalization_milestone",
                return_value=(milestone, ""),
            ))
            patches.enter_context(mock.patch.object(
                review,
                "is_native_problem_only_contract",
                return_value=True,
            ))
            patches.enter_context(mock.patch.object(
                review,
                "validate_native_resolved_answer_submission_current",
                resolved_validator,
            ))
            outcome = review._run_formalization_review_worker(
                spec,
                project_path=root,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
            )
        return outcome, resolved_validator

    def test_passed_review_rejects_operational_nonanswer(self) -> None:
        for review_certificate in (
            {"status": " passed "},
            {"verdict": "passed"},
        ):
            with self.subTest(review_certificate=review_certificate):
                with tempfile.TemporaryDirectory() as temp_dir:
                    outcome, resolved_validator = self._run_worker(
                        root=Path(temp_dir),
                        milestone={
                            "status": "solved",
                            "formalization_review": review_certificate,
                        },
                        resolution_error=(
                            "target answer submission is invalid: requested "
                            "output is an operational non-answer"
                        ),
                    )

                resolved_validator.assert_called_once()
                self.assertIsNone(outcome.milestone)
                self.assertIn(
                    "passing formalization_review requires a resolved answer "
                    "submission",
                    outcome.validation_error,
                )
                self.assertIn("operational non-answer", outcome.error)

    def test_failed_review_does_not_require_resolved_answer(self) -> None:
        milestone = {
            "status": "blocked",
            "formalization_review": {"status": "failed"},
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            outcome, resolved_validator = self._run_worker(
                root=Path(temp_dir),
                milestone=milestone,
                resolution_error="must not be consulted",
            )

        resolved_validator.assert_not_called()
        self.assertIs(outcome.milestone, milestone)
        self.assertEqual(outcome.validation_error, "")
        self.assertEqual(outcome.error, "")


if __name__ == "__main__":
    unittest.main()
