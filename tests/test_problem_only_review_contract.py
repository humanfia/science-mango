from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import Mock, patch

from archon.commands.loop.parallel_formalization_review import (
    _run_formalization_review_worker,
    build_target_formalization_review_prompt,
    load_target_formalization_milestone,
    run_parallel_formalization_reviews,
)
from archon.commands.loop.parallel_review import (
    PipelinedTargetReviewConfig,
    TargetReviewSpec,
    TargetReviewOutcome,
    _run_review_worker,
    build_target_review_prompt,
    load_pipelined_review_report,
    load_target_milestone,
    run_parallel_target_reviews,
    validate_parallel_review_session,
    write_parallel_review_session,
    write_pipelined_review_report,
)
from archon.commands.loop.prover.runners import ParallelProverRunner
from archon.commands.loop.problem_only_review_contract import (
    NATIVE_CONTRACT_KIND,
    ProblemOnlyReviewContractError,
    native_source_contract_provenance,
    resolve_target_review_source_contract,
    validate_native_review_source_certificate,
)


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _json_bytes(value: object) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


class ProblemOnlyReviewContractTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.project = Path(self.tempdir.name)
        self.state = self.project / ".archon"
        self.iter_dir = self.state / "logs" / "iter-001"
        self.output_root = self.iter_dir / "review"
        self.target = (
            self.project / "IChO2026Problems" / "problem_item_a.lean"
        )
        self.rel = "IChO2026Problems/problem_item_a.lean"
        self.lean_source = "theorem item_a : True := by trivial\n"
        self.image_rel = "icho_2026_source/image/page.png"
        self.bundle_rel = "icho_2026_source/questions_only.jsonl"
        self.report_rel = "reports/icho/problem_item_a.source.json"
        self.image_bytes = b"student-visible page; printed fallback -750"
        self.row = {
            "schema_version": 1,
            "protocol": "icho-answer-blind-v1",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "id": "item_a",
            "index": "item_a",
            "problem_id": "item",
            "part_id": "A",
            "question": (
                "Derive the upstream value from the givens. A later subpart "
                "prints fallback -750 for use only in that later subpart."
            ),
            "current_question": "Derive the upstream requested value.",
            "previous_parts": [],
            "requested_outputs": [{
                "id": "value",
                "kind": "integer",
                "source_requirement": "the independently derived value",
                "reporting_policy": {"kind": "exact_integer"},
            }],
            "problem_assets": [{
                "kind": "problem_page",
                "path": "page.png",
                "sha256": _sha256(self.image_bytes),
            }],
            "candidate_domain_policy": {
                "allowed_sources": [
                    "problem_text",
                    "problem_image",
                    "problem_stated_fallback",
                    "derived_theorem",
                ],
                "unjustified_search_bounds": "forbidden",
            },
            "measurement_policy": {
                "derived_tolerances": "prove_from_problem_intervals",
            },
            "reporting_policy": {
                "intermediate_rounding": "forbidden",
                "final_precision": {"kind": "per_requested_output"},
            },
        }
        self.preflight = {
            "file": self.rel,
            "status": "passed",
            "compiles": True,
            "returncode": 0,
            "sorry_count": 0,
            "duration_secs": 0.01,
            "diagnostics": "",
        }
        self._materialize_workspace()

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def _materialize_workspace(self) -> None:
        self.iter_dir.mkdir(parents=True, exist_ok=True)
        self.target.parent.mkdir(parents=True, exist_ok=True)
        self.target.write_text(self.lean_source, encoding="utf-8")
        image = self.project / self.image_rel
        image.parent.mkdir(parents=True, exist_ok=True)
        image.write_bytes(self.image_bytes)

        bundle_payload = _json_bytes(self.row)
        bundle = self.project / self.bundle_rel
        bundle.parent.mkdir(parents=True, exist_ok=True)
        bundle.write_bytes(bundle_payload)
        record_sha256 = _sha256(_json_bytes(self.row))

        entry = dict(self.row)
        entry.update({
            "blind_record_sha256": record_sha256,
            "image_paths": [self.image_rel],
            "image_path": self.image_rel,
        })
        report = {
            "schema_version": 3,
            "command": "physics-formalize",
            "domain": "chemistry",
            "evaluation_mode": "answer_blind",
            "lean_search_packages": ["Mathlib", "Physlib", "CRNT"],
            "next_stage": "autoformalize",
            "official_answer_seen": False,
            "phase": "solve",
            "status": "prepared",
            "path_base": "project",
            "project_path": ".",
            "proof_mode": "chemistry",
            "prover_mode": "chemistry-formalize",
            "output_lean": self.rel,
            "source_report": self.report_rel,
            "entry": entry,
            "problem_id": self.row["problem_id"],
            "part_id": self.row["part_id"],
            "previous_parts": self.row["previous_parts"],
            "blind_record_sha256": record_sha256,
        }
        report_path = self.project / self.report_rel
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(
            json.dumps(report, ensure_ascii=False),
            encoding="utf-8",
        )

        manifest = {
            "schema_version": 1,
            "protocol": "icho-problem-only-solver-seed-v1",
            "blind_bundle": {
                "path": self.bundle_rel,
                "row_count": 1,
                "sha256": _sha256(bundle_payload),
                "size": len(bundle_payload),
            },
            "blind_bundle_sha256": _sha256(bundle_payload),
            "assets": {self.image_rel: _sha256(self.image_bytes)},
        }
        (self.project / "isolation_manifest.json").write_text(
            json.dumps(manifest),
            encoding="utf-8",
        )

        self.state.mkdir(parents=True, exist_ok=True)
        config = {
            "answer_blind": {
                "protocol": "icho-answer-blind-v1",
                "phase": "solve",
                "authority": "problem-only",
                "official_answer_seen": False,
                "isolation": {
                    "filesystem_answer_blind": True,
                    "network_answer_blind": False,
                },
            },
            "loop": {"domain_profile": {"name": "chemistry-native"}},
        }
        (self.state / "config.json").write_text(
            json.dumps(config),
            encoding="utf-8",
        )

    def _contract(self) -> dict:
        return resolve_target_review_source_contract(
            project_path=self.project,
            target=self.target,
            preflight=self.preflight,
        )

    def _source_audit(self, contract: dict) -> dict:
        passed = {"status": "passed", "evidence": "bound evidence checked"}
        return {
            "source_contract": native_source_contract_provenance(contract),
            "blind_source_audit": {
                name: dict(passed)
                for name in (
                    "answer_independence",
                    "raw_derivation",
                    "reporting_rule_source",
                    "tolerance_provenance",
                    "candidate_domain_provenance",
                    "lean_result_binding",
                )
            },
            "contract_audit": {
                name: dict(passed)
                for name in (
                    "statement_scope",
                    "hypothesis_derivability",
                    "conclusion_alignment",
                    "bridge_completeness",
                )
            },
            "requested_outputs": [{
                "source_requirement": "the independently derived value",
                "lean_carrier": "item_a",
                "status": "covered",
                "evidence": "the declaration carries the requested value",
            }],
            "blueprint_conflicts": [],
            "image_audit": [{
                "path": image["path"],
                "sha256": image["sha256"],
                "inspected": True,
                "evidence": "the bound student-visible page was inspected",
            } for image in contract["images"]],
            "chemistry_checks": {
                name: dict(passed)
                for name in (
                    "chemical_semantics",
                    "formula_mass_consistency",
                    "conservation_laws",
                    "units_dimensions",
                    "numerical_reporting",
                    "structure_stereochemistry",
                    "identification_uniqueness",
                    "answer_smuggling",
                )
            },
        }

    def _proof_milestone(self, contract: dict) -> dict:
        return {
            "timestamp": "2026-08-16T00:00:00Z",
            "target": {"file": self.rel, "theorem": "item_a"},
            "status": "solved",
            "proof_review": {
                "schema_version": 1,
                "route": "solved",
                "reason": "bound source and proof passed",
                "evidence": "candidate and preflight hashes checked",
                "redraft_kind": "not_applicable",
                "infrastructure_request": None,
                **self._source_audit(contract),
            },
            "attempts": [],
            "findings": {
                "blocker": "",
                "verification": "bounded review",
                "key_lemmas_used": [],
            },
            "session": {"id": "session_1", "model": "test"},
            "next_steps": "",
        }

    def _formalization_milestone(self, contract: dict) -> dict:
        passed = {"status": "passed", "evidence": "bound evidence checked"}
        return {
            "timestamp": "2026-08-16T00:00:00Z",
            "target": {"file": self.rel, "theorem": "item_a"},
            "status": "solved",
            "formalization_review": {
                "schema_version": 2,
                "status": "passed",
                "reason": "bound source and statement passed",
                "checks": {
                    name: dict(passed)
                    for name in (
                        "source_faithfulness",
                        "derivability",
                        "abstraction_sufficiency",
                        "countermodel_resistance",
                    )
                } | {
                    "uncertainty_propagation": {
                        "status": "not_applicable",
                        "evidence": "no uncertainty requested",
                    },
                    "branch_orientation": {
                        "status": "not_applicable",
                        "evidence": "no branch requested",
                    },
                },
                "bridge_obligations": [{
                    "claim": "problem relation",
                    "carrier": "item_a",
                    "status": "covered",
                    "evidence": "the declaration carries the relation",
                }],
                **self._source_audit(contract),
            },
            "attempts": [],
            "findings": {
                "blocker": "",
                "verification": "bounded review",
                "key_lemmas_used": [],
            },
            "session": {"id": "session_1", "model": "test"},
            "next_steps": "",
        }

    def test_contract_hash_binds_only_native_problem_inputs(self) -> None:
        contract = self._contract()
        self.assertEqual(contract["contract_kind"], NATIVE_CONTRACT_KIND)
        self.assertEqual(contract["authority"], "problem-only")
        self.assertEqual(contract["evaluation_mode"], "answer_blind")
        self.assertEqual(contract["candidate"], self.rel)
        self.assertEqual(
            contract["candidate_sha256"], _sha256(self.target.read_bytes()),
        )
        self.assertEqual(len(contract["preflight_sha256"]), 64)
        self.assertEqual(contract["images"][0]["path"], self.image_rel)
        for forbidden in (
            "blueprint",
            "trace",
            "task_results",
            "prior_gate",
            "blind_candidate_record",
        ):
            self.assertNotIn(forbidden, contract)

    def test_native_prompts_do_not_read_or_render_legacy_artifacts(self) -> None:
        contract = self._contract()
        slug = "IChO2026Problems_problem_item_a"
        artifacts = (
            self.project / "blueprint" / "src" / "chapters" / f"{slug}.tex",
            self.iter_dir / "provers" / f"{slug}.jsonl",
            self.iter_dir / "formalizers" / f"{slug}.jsonl",
            self.state / "task_results" / "problem_item_a.lean.md",
        )
        for index, artifact in enumerate(artifacts):
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_text(
                f"LEGACY_ARTIFACT_SECRET_{index}",
                encoding="utf-8",
            )
        prior = {"sentinel": "PRIOR_GATE_SECRET"}

        with patch(
            "archon.commands.loop.parallel_review.load_domain_profile",
            side_effect=AssertionError("native prompt touched legacy profile"),
        ):
            proof_prompt = build_target_review_prompt(
                project_path=self.project,
                state_dir=self.state,
                iter_dir=self.iter_dir,
                iter_num=1,
                target=self.target,
                output_dir=self.output_root / "proof",
                preflight=self.preflight,
                prior_gate_record=prior,
                source_contract=contract,
            )
        with (
            patch(
                "archon.commands.loop.parallel_formalization_review."
                "_result_evidence",
                side_effect=AssertionError("native prompt read task results"),
            ),
            patch(
                "archon.commands.loop.parallel_formalization_review."
                "load_domain_profile",
                side_effect=AssertionError("native prompt touched legacy profile"),
            ),
        ):
            formal_prompt = build_target_formalization_review_prompt(
                project_path=self.project,
                state_dir=self.state,
                iter_dir=self.iter_dir,
                iter_num=1,
                target=self.target,
                output_dir=self.output_root / "formalization",
                preflight=self.preflight,
                prior_gate_record=prior,
                source_contract=contract,
            )

        for prompt in (proof_prompt, formal_prompt):
            self.assertIn("NATIVE PROBLEM-INPUT-ONLY CONTRACT", prompt)
            self.assertIn("candidate_sha256", prompt)
            self.assertNotIn("preflight_sha256", prompt)
            self.assertIn("printed fallback", prompt)
            self.assertIn("never use a later fallback backward", prompt)
            self.assertNotIn("PRIOR_GATE_SECRET", prompt)
            self.assertNotIn(str(self.project / self.report_rel), prompt)
            self.assertNotIn("Bound problem-side source report", prompt)
            for artifact in artifacts:
                self.assertNotIn(str(artifact), prompt)
            for marker in (
                "LEGACY_ARTIFACT_SECRET",
                "OFFICIAL SOURCE CONTRACT",
                "official_answer_alignment",
                "entry.answer (official rubric)",
                "Blind solve candidate record",
                "blind_candidates",
                "frozen before any later reveal",
            ):
                self.assertNotIn(marker, prompt)

    def test_native_certificate_binds_exact_provenance(self) -> None:
        contract = self._contract()
        audit = self._source_audit(contract)
        self.assertEqual(
            validate_native_review_source_certificate(
                audit, contract, passing=True,
            ),
            "",
        )
        audit["source_contract"]["candidate_sha256"] = "0" * 64
        self.assertIn(
            "does not match native problem-only evidence",
            validate_native_review_source_certificate(
                audit, contract, passing=True,
            ),
        )

    def test_answer_bearing_keys_and_ambiguous_reports_fail_closed(self) -> None:
        self.row["nested"] = {"official_solution": "secret"}
        self._materialize_workspace()
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "answer-bearing field",
        ):
            self._contract()

        self.row.pop("nested")
        self._materialize_workspace()
        duplicate = (
            self.project / "reports" / "duplicate"
            / "problem_item_a.source.json"
        )
        duplicate.parent.mkdir(parents=True)
        duplicate.write_bytes((self.project / self.report_rel).read_bytes())
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "exactly one matching",
        ):
            self._contract()

    def test_native_config_and_preflight_fail_closed(self) -> None:
        config_path = self.state / "config.json"
        config = json.loads(config_path.read_text(encoding="utf-8"))
        config.pop("answer_blind")
        config_path.write_text(json.dumps(config), encoding="utf-8")
        calls = 0

        def worker(*_args, **_kwargs):
            nonlocal calls
            calls += 1
            raise AssertionError("worker must not start")

        report = run_parallel_target_reviews(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target],
            preflight={"targets": [self.preflight]},
            prior_gate_targets={},
            requested_jobs=1,
            max_attempts=1,
            backoff_sec=0,
            verbose_logs=False,
            model=None,
            backend=None,
            harness=None,
            worker_fn=worker,
            executor_factory=ThreadPoolExecutor,
        )
        self.assertEqual(calls, 0)
        self.assertFalse(report["complete"])
        self.assertEqual(report["unresolved"], [self.rel])

        self._materialize_workspace()
        incomplete = dict(self.preflight)
        incomplete.pop("diagnostics")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "missing or ambiguous fields",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=incomplete,
            )

    def test_config_symlink_is_rejected_but_legacy_supplied_contract_remains(self) -> None:
        config_path = self.state / "config.json"
        config_payload = config_path.read_bytes()
        config_path.unlink()
        real_config = self.project / "real-config.json"
        real_config.write_bytes(config_payload)
        config_path.symlink_to(real_config)
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "may not traverse a symlink",
        ):
            self._contract()

        config_path.unlink()
        config_path.write_text(
            json.dumps({"loop": {"domain_profile": {"name": "chemistry"}}}),
            encoding="utf-8",
        )
        supplied = {"legacy": "unchanged"}
        resolved = resolve_target_review_source_contract(
            project_path=self.project,
            target=self.target,
            preflight={},
            supplied_contract=supplied,
        )
        self.assertIs(resolved, supplied)

    def test_pre_worker_input_drift_ignores_valid_stale_milestone(self) -> None:
        cases = (
            (
                "proof",
                _run_review_worker,
                load_target_milestone,
                self._proof_milestone,
                "archon.commands.loop.parallel_review.build_runner",
            ),
            (
                "formalization",
                _run_formalization_review_worker,
                load_target_formalization_milestone,
                self._formalization_milestone,
                "archon.commands.loop.parallel_formalization_review.build_runner",
            ),
        )
        for name, worker, loader, make_row, patch_path in cases:
            with self.subTest(name=name):
                self.target.write_text(self.lean_source, encoding="utf-8")
                contract = self._contract()
                output = self.output_root / name / "pre"
                output.mkdir(parents=True, exist_ok=True)
                milestone = output / "milestones.jsonl"
                milestone.write_text(
                    json.dumps(make_row(contract)) + "\n",
                    encoding="utf-8",
                )
                self.assertEqual(loader(milestone, self.rel, contract)[1], "")
                self.target.write_text(
                    self.lean_source + "-- input drift\n",
                    encoding="utf-8",
                )
                spec = TargetReviewSpec(
                    rel=self.rel,
                    prompt="bounded prompt",
                    output_dir=str(output),
                    log_base=str(output / "agent"),
                    attempt=1,
                    source_contract=contract,
                )
                with patch(patch_path) as build:
                    outcome = worker(
                        spec,
                        project_path=self.project,
                        verbose_logs=False,
                        model=None,
                        backend=None,
                        harness=None,
                    )
                build.assert_not_called()
                self.assertIsNone(outcome.milestone)
                self.assertIn("changed after contract creation", outcome.error)

    def test_post_worker_input_drift_ignores_valid_stale_milestone(self) -> None:
        cases = (
            (
                "proof",
                _run_review_worker,
                load_target_milestone,
                self._proof_milestone,
                "archon.commands.loop.parallel_review.build_runner",
            ),
            (
                "formalization",
                _run_formalization_review_worker,
                load_target_formalization_milestone,
                self._formalization_milestone,
                "archon.commands.loop.parallel_formalization_review.build_runner",
            ),
        )
        for name, worker, loader, make_row, patch_path in cases:
            with self.subTest(name=name):
                self.target.write_text(self.lean_source, encoding="utf-8")
                contract = self._contract()
                output = self.output_root / name / "post"
                output.mkdir(parents=True, exist_ok=True)
                milestone = output / "milestones.jsonl"
                milestone.write_text(
                    json.dumps(make_row(contract)) + "\n",
                    encoding="utf-8",
                )
                self.assertEqual(loader(milestone, self.rel, contract)[1], "")
                runner = Mock()

                def mutate_candidate(*_args, **_kwargs):
                    self.target.write_text(
                        self.lean_source + "-- worker drift\n",
                        encoding="utf-8",
                    )
                    return True

                runner.run.side_effect = mutate_candidate
                spec = TargetReviewSpec(
                    rel=self.rel,
                    prompt="bounded prompt",
                    output_dir=str(output),
                    log_base=str(output / "agent"),
                    attempt=1,
                    source_contract=contract,
                )
                with patch(patch_path, return_value=runner):
                    outcome = worker(
                        spec,
                        project_path=self.project,
                        verbose_logs=False,
                        model=None,
                        backend=None,
                        harness=None,
                    )
                runner.run.assert_called_once()
                self.assertTrue(outcome.runner_ok)
                self.assertIsNone(outcome.milestone)
                self.assertIn("changed after contract creation", outcome.error)


    def test_requested_outputs_require_exact_one_to_one_coverage(self) -> None:
        self.row["requested_outputs"].append({
            "id": "second_value",
            "kind": "integer",
            "source_requirement": "the independently derived second value",
            "reporting_policy": {"kind": "exact_integer"},
        })
        self._materialize_workspace()
        contract = self._contract()
        audit = self._source_audit(contract)
        audit["requested_outputs"].append({
            "source_requirement": "the independently derived second value",
            "lean_carrier": "item_a_second",
            "status": "covered",
            "evidence": "the second declaration carries the value",
        })
        self.assertEqual(
            validate_native_review_source_certificate(
                audit, contract, passing=True,
            ),
            "",
        )

        variants = {}
        missing = json.loads(json.dumps(audit))
        missing["requested_outputs"].pop()
        variants["missing"] = missing
        duplicate = json.loads(json.dumps(audit))
        duplicate["requested_outputs"][1] = dict(
            duplicate["requested_outputs"][0]
        )
        variants["duplicate"] = duplicate
        bogus = json.loads(json.dumps(audit))
        bogus["requested_outputs"][1]["source_requirement"] = "bogus"
        variants["bogus"] = bogus
        blocked = json.loads(json.dumps(audit))
        blocked["requested_outputs"][1]["status"] = "blocked"
        variants["blocked"] = blocked
        for name, review in variants.items():
            with self.subTest(name=name):
                self.assertNotEqual(
                    validate_native_review_source_certificate(
                        review, contract, passing=True,
                    ),
                    "",
                )

    def test_source_report_pollution_and_nonfinite_evidence_fail_closed(self) -> None:
        report_path = self.project / self.report_rel
        report = json.loads(report_path.read_text(encoding="utf-8"))
        report["notes"] = "unbound generated note"
        report_path.write_text(json.dumps(report), encoding="utf-8")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "unexpected or missing fields",
        ):
            self._contract()

        self._materialize_workspace()
        bad_preflight = dict(self.preflight)
        bad_preflight["duration_secs"] = float("inf")
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "diagnostics are invalid",
        ):
            resolve_target_review_source_contract(
                project_path=self.project,
                target=self.target,
                preflight=bad_preflight,
            )

        self.row["measurement_policy"]["nonfinite"] = float("nan")
        self._materialize_workspace()
        with self.assertRaisesRegex(
            ProblemOnlyReviewContractError, "non-finite JSON constant",
        ):
            self._contract()

    def test_bad_target_does_not_block_good_target_in_either_batch(self) -> None:
        bad = self.target.with_name("problem_missing.lean")
        bad.write_text(self.lean_source, encoding="utf-8")
        bad_rel = bad.relative_to(self.project).as_posix()
        bad_preflight = {**self.preflight, "file": bad_rel}

        proof_calls: list[str] = []

        def proof_worker(spec, **_kwargs):
            proof_calls.append(spec.rel)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._proof_milestone(spec.source_contract),
            )

        proof_report = run_parallel_target_reviews(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target, bad],
            preflight={"targets": [self.preflight, bad_preflight]},
            prior_gate_targets={},
            requested_jobs=2,
            max_attempts=1,
            backoff_sec=0,
            verbose_logs=False,
            model=None,
            backend=None,
            harness=None,
            worker_fn=proof_worker,
            executor_factory=ThreadPoolExecutor,
        )
        self.assertFalse(proof_report["complete"])
        self.assertEqual(proof_report["reviewed"], 1)
        self.assertEqual(proof_report["unresolved"], [bad_rel])
        self.assertEqual(proof_calls, [self.rel])

        formal_calls: list[str] = []

        def formal_worker(spec, **_kwargs):
            formal_calls.append(spec.rel)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._formalization_milestone(spec.source_contract),
            )

        formal_report = run_parallel_formalization_reviews(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target, bad],
            preflight={"targets": [self.preflight, bad_preflight]},
            prior_gate_targets={},
            requested_jobs=2,
            max_attempts=1,
            backoff_sec=0,
            verbose_logs=False,
            model=None,
            backend=None,
            harness=None,
            worker_fn=formal_worker,
            executor_factory=ThreadPoolExecutor,
        )
        self.assertFalse(formal_report["complete"])
        self.assertEqual(formal_report["reviewed"], 1)
        self.assertEqual(formal_report["unresolved"], [bad_rel])
        self.assertEqual(formal_calls, [self.rel])

    def test_lifecycle_keeps_formal_contract_after_proof_body_change(self) -> None:
        (self.iter_dir / "provers").mkdir(parents=True, exist_ok=True)
        (self.state / "task_results").mkdir(parents=True, exist_ok=True)
        (self.iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")
        formal_contracts: list[dict] = []
        proof_contracts: list[dict] = []

        def preflight_checker(*, project_path, target, timeout_sec):
            del project_path, timeout_sec
            source = target.read_text(encoding="utf-8")
            return {
                **self.preflight,
                "sorry_count": source.count("sorry"),
            }

        def formalizer(*_args, **_kwargs):
            self.target.write_text(
                "theorem item_a : True := by sorry\n", encoding="utf-8",
            )
            result = self.state / "task_results" / "problem_item_a.lean.md"
            result.write_text("# Native redraft\n", encoding="utf-8")
            return True

        def formal_review(spec, **_kwargs):
            formal_contracts.append(spec.source_contract)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._formalization_milestone(spec.source_contract),
            )

        def prover(*_args, **_kwargs):
            self.target.write_text(self.lean_source, encoding="utf-8")
            return True

        def proof_review(spec, **_kwargs):
            proof_contracts.append(spec.source_contract)
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=self._proof_milestone(spec.source_contract),
            )

        runner = ParallelProverRunner(
            project_name="project",
            project_path=self.project,
            state_dir=self.state,
            stage="autoformalize",
            iter_dir=self.iter_dir,
            iter_meta=self.iter_dir / "meta.json",
            iter_num=1,
            max_parallel=1,
            max_objectives=1,
            block_on_blocked_deps=False,
            verbose_logs=False,
            model="test",
            pipeline_review=PipelinedTargetReviewConfig(
                requested_jobs=1,
                max_attempts=1,
                backoff_sec=0,
                formalization_review_enabled=True,
                formalization_review_max_attempts=1,
                formalization_review_backoff_sec=0,
            ),
            executor_factory=ThreadPoolExecutor,
            prover_worker=prover,
            review_worker=proof_review,
            formalization_review_worker=formal_review,
            formalizer_worker=formalizer,
            preflight_checker=preflight_checker,
        )
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="work",
            ),
            patch("archon.commands.loop.prover.runners.snapshot_baseline"),
            patch(
                "archon.commands.loop.prover.runners.pick_resume_session",
                return_value=None,
            ),
            patch("archon.commands.loop.prover.runners.persist_session_id"),
        ):
            runner._run_fanout([self.target], file_modes={})

        self.assertEqual(len(formal_contracts), 1)
        self.assertEqual(len(proof_contracts), 1)
        self.assertNotEqual(
            formal_contracts[0]["candidate_sha256"],
            proof_contracts[0]["candidate_sha256"],
        )
        report = json.loads(
            (self.iter_dir / "pipelined-review.json").read_text(
                encoding="utf-8",
            )
        )
        self.assertTrue(report["complete"])
        self.assertTrue(report["gate_events_applied"])
        self.assertEqual(
            [event["kind"] for event in report["gate_events"]],
            ["formalization", "proof"],
        )
        formal_gate = json.loads(
            (self.state / "formalization-review-gate.json").read_text(
                encoding="utf-8",
            )
        )
        proof_gate = json.loads(
            (self.state / "proof-review-gate.json").read_text(
                encoding="utf-8",
            )
        )
        self.assertEqual(formal_gate["targets"][self.rel]["status"], "passed")
        self.assertEqual(proof_gate["targets"][self.rel]["status"], "solved")

    def test_changed_incomplete_redraft_evicts_stale_proof_outcome(self) -> None:
        (self.iter_dir / "provers").mkdir(parents=True, exist_ok=True)
        (self.state / "task_results").mkdir(parents=True, exist_ok=True)
        (self.iter_dir / "meta.json").write_text("{}\n", encoding="utf-8")

        def preflight_checker(*, project_path, target, timeout_sec):
            del project_path, target, timeout_sec
            return dict(self.preflight)

        def proof_review(spec, **_kwargs):
            milestone = self._proof_milestone(spec.source_contract)
            milestone["status"] = "blocked"
            milestone["proof_review"].update({
                "route": "needs_redraft",
                "reason": "the statement must be redrafted",
                "evidence": "the candidate statement omits a source relation",
                "redraft_kind": "other_modeling_defect",
            })
            return TargetReviewOutcome(
                rel=spec.rel,
                attempt=spec.attempt,
                runner_ok=True,
                milestone=milestone,
            )

        def incomplete_formalizer(*_args, **_kwargs):
            self.target.write_text(
                self.lean_source + "-- changed without a task result\n",
                encoding="utf-8",
            )
            return True

        def unexpected_formal_review(*_args, **_kwargs):
            raise AssertionError("incomplete redraft must not be reviewed")

        runner = ParallelProverRunner(
            project_name="project",
            project_path=self.project,
            state_dir=self.state,
            stage="prover",
            iter_dir=self.iter_dir,
            iter_meta=self.iter_dir / "meta.json",
            iter_num=1,
            max_parallel=1,
            max_objectives=1,
            block_on_blocked_deps=False,
            verbose_logs=False,
            model="test",
            pipeline_review=PipelinedTargetReviewConfig(
                requested_jobs=1,
                max_attempts=1,
                backoff_sec=0,
                formalization_review_enabled=True,
                formalization_review_max_attempts=1,
                formalization_review_backoff_sec=0,
            ),
            executor_factory=ThreadPoolExecutor,
            prover_worker=lambda *_args, **_kwargs: True,
            review_worker=proof_review,
            formalization_review_worker=unexpected_formal_review,
            formalizer_worker=incomplete_formalizer,
            preflight_checker=preflight_checker,
        )
        with (
            patch(
                "archon.commands.loop.prover.runners."
                "build_parallel_prover_prompt",
                return_value="work",
            ),
            patch("archon.commands.loop.prover.runners.snapshot_baseline"),
            patch(
                "archon.commands.loop.prover.runners.pick_resume_session",
                return_value=None,
            ),
            patch("archon.commands.loop.prover.runners.persist_session_id"),
        ):
            runner._run_fanout([self.target], file_modes={})

        report = json.loads(
            (self.iter_dir / "pipelined-review.json").read_text(
                encoding="utf-8",
            )
        )
        self.assertTrue(report["complete"])
        self.assertEqual(report["proof_review_target_files"], [])
        self.assertEqual(report["reviewed"], 0)
        self.assertTrue(report["formalizer_results"][self.rel]["changed"])
        self.assertFalse(
            report["formalizer_results"][self.rel]["task_result_updated"],
        )
        session = (
            self.state / "proof-journal" / "sessions" / "session_1"
            / "milestones.jsonl"
        )
        self.assertEqual(session.read_text(encoding="utf-8"), "")

    def test_durable_native_session_rejects_stale_source_and_preflight(self) -> None:
        contract = self._contract()
        milestone = self._proof_milestone(contract)
        nested = milestone.pop("proof_review")
        milestone["findings"]["proof_review"] = nested
        outcome = TargetReviewOutcome(
            rel=self.rel,
            attempt=1,
            runner_ok=True,
            milestone=milestone,
        )
        session_dir = (
            self.state / "proof-journal" / "sessions" / "session_1"
        )
        write_parallel_review_session(
            session_dir=session_dir,
            iter_num=1,
            outcomes={self.rel: outcome},
        )
        self.assertEqual(
            validate_parallel_review_session(
                session_dir=session_dir,
                expected_rels=[self.rel],
                project_path=self.project,
            ),
            "",
        )

        preflight = {
            "iteration": 1,
            "jobs": 1,
            "duration_secs": self.preflight["duration_secs"],
            "summary": {"total": 1, "passed": 1, "failed": 0},
            "targets": [self.preflight],
        }
        report = {
            "iteration": 1,
            "complete": True,
            "status": "complete",
            "pipeline_mode": "target_lifecycle",
            "starts_at": "formalizer",
            "target_files": [self.rel],
            "settled_target_files": [self.rel],
            "proof_review_target_files": [self.rel],
            "targets": 1,
            "reviewed": 1,
            "unresolved": [],
            "preflight": preflight,
            "gate_events_applied": False,
        }
        write_pipelined_review_report(iter_dir=self.iter_dir, report=report)
        loaded, error = load_pipelined_review_report(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target],
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(loaded)

        self.target.write_text(
            self.lean_source + "-- stale candidate\n", encoding="utf-8",
        )
        self.assertIn(
            "does not match native problem-only evidence",
            validate_parallel_review_session(
                session_dir=session_dir,
                expected_rels=[self.rel],
                project_path=self.project,
            ),
        )
        self.target.write_text(self.lean_source, encoding="utf-8")

        failed_row = {
            **self.preflight,
            "status": "failed",
            "compiles": False,
            "returncode": 1,
            "sorry_count": 0,
            "diagnostics": "compile failed",
        }
        report["preflight"] = {
            **preflight,
            "summary": {"total": 1, "passed": 0, "failed": 1},
            "targets": [failed_row],
        }
        write_pipelined_review_report(iter_dir=self.iter_dir, report=report)
        loaded, error = load_pipelined_review_report(
            project_path=self.project,
            state_dir=self.state,
            iter_dir=self.iter_dir,
            iter_num=1,
            objectives=[self.target],
        )
        self.assertIsNone(loaded)
        self.assertIn("lacks successful", error)

if __name__ == "__main__":
    unittest.main()
