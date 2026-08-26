from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest import mock

import archon.commands.loop.parallel_formalization_review as parallel_formalization_review
from archon.commands.loop.answer_submission import answer_submission_path
from archon.commands.loop.native_semantic_review import (
    build_independent_rederivation_example,
    build_native_semantic_review_contract,
)
from archon.commands.loop.parallel_formalization_review import (
    _write_session,
    build_target_formalization_review_prompt,
    load_target_formalization_milestone,
    run_parallel_formalization_reviews,
)
from archon.commands.loop.parallel_review import TargetReviewOutcome


def _blind_contract(rel: str) -> dict:
    digest = "b" * 64
    return {
        "schema_version": 3,
        "required": True,
        "available": True,
        "valid": True,
        "domain": "chemistry",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "authority": "problem-only",
        "target": rel,
        "lean_sha256": digest,
        "blueprint": "blueprint.tex",
        "blueprint_sha256": digest,
        "source_report": "problem.source.json",
        "source_sha256": digest,
        "entry_id": "problem_a",
        "blind_record_sha256": digest,
        "blind_candidate_record": "blind_candidates/problem_a.json",
        "blind_candidate_sha256": digest,
        "lean_result_contracts_sha256": digest,
        "question_field": "question",
        "question_sha256": digest,
        "previous_blind_sha256": digest,
        "previous_blind_hashes": [],
        "images": [],
        "errors": [],
        "problem_evidence": {
            "current_question": "Compute the requested quantity.",
            "previous_parts": [],
        },
    }


def _milestone(rel: str, *, passed: bool = True) -> dict:
    checks = {
        "source_faithfulness": {
            "status": "passed" if passed else "failed",
            "evidence": "the source quantity is represented explicitly",
        },
        "derivability": {
            "status": "passed",
            "evidence": "the conclusion follows without assuming the answer",
        },
        "abstraction_sufficiency": {
            "status": "passed",
            "evidence": "the model retains every relevant degree of freedom",
        },
        "uncertainty_propagation": {
            "status": "not_applicable",
            "evidence": "the source has no uncertainty calculation",
        },
        "branch_orientation": {
            "status": "not_applicable",
            "evidence": "the source has no branch choice",
        },
        "countermodel_resistance": {
            "status": "passed",
            "evidence": "no countermodel survives the explicit assumptions",
        },
    }
    return {
        "timestamp": "2026-07-28T00:00:00Z",
        "target": {"file": rel, "theorem": "example"},
        "status": "solved" if passed else "blocked",
        "formalization_review": {
            "schema_version": 2,
            "status": "passed" if passed else "failed",
            "reason": (
                "the contract is faithful"
                if passed else "the contract omits a source constraint"
            ),
            "checks": checks,
            "bridge_obligations": [{
                "claim": "source relation",
                "carrier": "hypothesis h_relation",
                "status": "covered",
                "evidence": "h_relation is used in the target derivation",
            }],
        },
        "attempts": [{
            "attempt": 1,
            "strategy": "formalization-review",
            "code_tried": "",
            "lean_error": "",
            "goal_before": "",
            "goal_after": "",
            "result": "success" if passed else "failed",
            "insight": "semantic contract inspected",
        }],
        "findings": {
            "blocker": "" if passed else "missing source constraint",
            "verification": "bounded semantic review",
            "key_lemmas_used": [],
        },
        "session": {"id": "session_1", "model": "test"},
        "next_steps": "" if passed else "restore the missing constraint",
    }


def _canonical_json_bytes(value: object) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _native_preflight(root: Path, rel: str) -> dict:
    return {
        "file": rel,
        "status": "passed",
        "compiles": True,
        "returncode": 0,
        "sorry_count": 1,
        "duration_secs": 0.01,
        "diagnostics": "",
        "numeric_reporting": {
            "active": True,
            "status": "passed",
            "reason": "trusted numeric reporting checks passed",
            "numeric_outputs": 1,
            "lean_source_sha256": hashlib.sha256(
                (root / rel).read_bytes()
            ).hexdigest(),
            "bundle_sha256": hashlib.sha256(
                (root / "icho_2026_source/questions_only.jsonl").read_bytes()
            ).hexdigest(),
            "certificates": [{
                "output_id": "amount",
                "reporting_policy_kind": "significant_figures",
                "reporting_policy_digits": 3,
                "reported_value": "1",
                "reporting_quantum": "1/100",
                "raw_declaration": "Example.rawAmount",
                "reporting_declaration": "Example.reportingProof",
            }],
            "lean_probe_passed": True,
        },
    }


def _materialize_native_target(root: Path, target: Path, row: dict) -> None:
    rel = target.relative_to(root).as_posix()
    report_rel = f"reports/icho/{target.stem}.source.json"
    record_sha256 = hashlib.sha256(_canonical_json_bytes(row)).hexdigest()
    image_paths = [
        f"icho_2026_source/image/{asset['path']}"
        for asset in row["problem_assets"]
        if asset["kind"] == "problem_page"
    ]
    entry = dict(row)
    entry.update({
        "blind_record_sha256": record_sha256,
        "image_paths": image_paths,
        "image_path": image_paths[0],
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
        "output_lean": rel,
        "source_report": report_rel,
        "entry": entry,
        "problem_id": row["problem_id"],
        "part_id": row["part_id"],
        "previous_parts": row["previous_parts"],
        "blind_record_sha256": record_sha256,
    }
    report_path = root / report_rel
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report), encoding="utf-8")
    answer_path = answer_submission_path(root, row["id"])
    answer_path.parent.mkdir(parents=True, exist_ok=True)
    answer_path.write_text(json.dumps({
        "schema_version": 1,
        "id": row["id"],
        "official_answer_seen": False,
        "outputs": [{
            "id": "amount",
            "kind": "numeric",
            "raw_value": "7/2",
            "display_value": "3.50",
            "unit": "mol",
        }],
    }), encoding="utf-8")


def _native_project(root: Path) -> tuple[Path, dict]:
    state = root / ".archon"
    state.mkdir()
    (state / "config.json").write_text(json.dumps({
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
        "loop": {
            "domain_profile": {
                "name": "chemistry-native",
                "lean_search_packages": ["Mathlib", "Physlib", "CRNT"],
            }
        }
    }))
    target = root / "IChO2026Problems/problem_native_a.lean"
    target.parent.mkdir()
    target.write_text("theorem nativeA : True := by sorry\n")
    image_bytes = b"problem-only page"
    image_sha = hashlib.sha256(image_bytes).hexdigest()
    image = root / "icho_2026_source/image/page.png"
    image.parent.mkdir(parents=True)
    image.write_bytes(image_bytes)
    row = {
        "schema_version": 1,
        "protocol": "icho-answer-blind-v1",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "phase": "solve",
        "id": "native_a",
        "index": "native_a",
        "problem_id": "native",
        "part_id": "A",
        "question": "Use the printed source relation.",
        "current_question": "Find the requested amount.",
        "shared_context": "Keep intermediate values exact.",
        "previous_parts": [],
        "images": ["page.png"],
        "problem_assets": [{
            "kind": "problem_page", "path": "page.png", "sha256": image_sha,
        }],
        "requested_outputs": [{
            "id": "amount",
            "source_requirement": "the requested amount",
            "kind": "numeric",
            "unit": "mol",
            "reporting_policy": {"kind": "significant_figures", "digits": 3},
        }],
        "reporting_policy": {
            "intermediate_rounding": "forbidden",
            "final_precision": {"kind": "significant_figures", "digits": 3},
            "tie_rule": "half_away_from_zero",
        },
        "measurement_policy": {"stipulated_constants": "exact_as_printed"},
        "candidate_domain_policy": {
            "underdetermined_result": "must_be_reported",
        },
    }
    bundle = root / "icho_2026_source/questions_only.jsonl"
    payload = (json.dumps(row) + "\n").encode()
    bundle.write_bytes(payload)
    digest = hashlib.sha256(payload).hexdigest()
    _materialize_native_target(root, target, row)
    (root / "isolation_manifest.json").write_text(json.dumps({
        "schema_version": 1,
        "protocol": "icho-problem-only-solver-seed-v1",
        "blind_bundle": {
            "path": "icho_2026_source/questions_only.jsonl",
            "row_count": 1,
            "sha256": digest,
            "size": len(payload),
        },
        "blind_bundle_sha256": digest,
        "target_ids": ["native_a"],
        "assets": {"icho_2026_source/image/page.png": image_sha},
    }))
    contract = build_native_semantic_review_contract(
        project_path=root,
        target=target,
    )
    assert isinstance(contract, dict) and contract["valid"]
    return target, contract


def _native_project_pair(root: Path) -> list[tuple[Path, dict]]:
    first_target, _first_contract = _native_project(root)
    bundle = root / "icho_2026_source/questions_only.jsonl"
    first_row = json.loads(bundle.read_text(encoding="utf-8"))
    second_row = json.loads(json.dumps(first_row))
    second_row["id"] = "native_b"
    second_row["index"] = "native_b"
    second_row["part_id"] = "B"
    second_row["question"] = "Use the second printed source relation."
    second_target = root / "IChO2026Problems/problem_native_b.lean"
    second_target.write_text("theorem nativeB : True := by sorry\n")
    _materialize_native_target(root, second_target, second_row)
    payload = (
        json.dumps(first_row) + "\n" + json.dumps(second_row) + "\n"
    ).encode("utf-8")
    bundle.write_bytes(payload)
    digest = hashlib.sha256(payload).hexdigest()
    manifest_path = root / "isolation_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["blind_bundle"].update({
        "row_count": 2,
        "sha256": digest,
        "size": len(payload),
    })
    manifest["blind_bundle_sha256"] = digest
    manifest["target_ids"] = ["native_a", "native_b"]
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    result = []
    for target in (first_target, second_target):
        contract = build_native_semantic_review_contract(
            project_path=root,
            target=target,
        )
        assert isinstance(contract, dict) and contract["valid"]
        result.append((target, contract))
    return result


def _native_milestone(rel: str, contract: dict) -> dict:
    milestone = _milestone(rel)
    milestone["formalization_review"]["independent_rederivation"] = (
        build_independent_rederivation_example(contract)
    )
    return milestone


def _r10_invalid_native_milestone(
    rel: str, contract: dict, defect: str,
) -> dict:
    milestone = _native_milestone(rel, contract)
    output = milestone["formalization_review"]["independent_rederivation"][
        "requested_outputs"
    ][0]
    if defect == "missing_unit":
        output["constants"] = [{
            "name": "source factor",
            "value": 1,
            "source_locator": {
                "kind": "problem_text",
                "reference": "shared_context",
            },
        }]
    elif defect == "unsupported_scope":
        output["process_scope"]["kind"] = "OFFICIAL_ANSWER_SENTINEL"
    elif defect == "extra_role":
        output["constants"] = [{
            "name": "source factor",
            "value": 1,
            "unit": "dimensionless",
            "source_locator": {
                "kind": "problem_text",
                "reference": "shared_context",
            },
            "role": "PRIOR_DERIVATION_SENTINEL",
        }]
    elif defect == "unsupported_dependency":
        output["dependencies"] = [{
            "kind": "OFFICIAL_ANSWER_SENTINEL",
            "reference": "printed relation",
            "relation": "source quantity enters the governing relation",
            "source_locator": {
                "kind": "problem_text",
                "reference": "shared_context",
            },
        }]
    else:
        raise ValueError(f"unknown defect: {defect}")
    output["raw_result"]["derivation"] = "PRIOR_DERIVATION_SENTINEL"
    return milestone


class ParallelFormalizationReviewTest(unittest.TestCase):
    def test_session_summary_normalizes_status_and_verdict(self):
        with tempfile.TemporaryDirectory() as td:
            session = Path(td)
            outcomes = {}
            for rel, review in (
                ("A.lean", {"status": " PASSED "}),
                ("B.lean", {"verdict": "passed"}),
            ):
                outcomes[rel] = TargetReviewOutcome(
                    rel=rel,
                    attempt=1,
                    runner_ok=True,
                    milestone={
                        "target": {"file": rel},
                        "formalization_review": review,
                    },
                )
            _write_session(
                session_dir=session,
                iter_num=1,
                outcomes=outcomes,
            )
            self.assertIn(
                "- Passed: 2",
                (session / "summary.md").read_text(encoding="utf-8"),
            )
            self.assertIn(
                "No formalization redrafts requested.",
                (session / "recommendations.md").read_text(encoding="utf-8"),
            )
    def test_native_prompt_is_problem_only_source_first_and_target_scoped(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target, contract = _native_project(root)
            state = root / ".archon"
            iter_dir = state / "logs/iter-001"
            output = iter_dir / "formalization-review-targets/native/attempt-1"

            prompt = build_target_formalization_review_prompt(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=1,
                target=target,
                output_dir=output,
                preflight=_native_preflight(
                    root, target.relative_to(root).as_posix(),
                ),
                prior_gate_record={"reason": "OLD_CANDIDATE_BIAS_SENTINEL"},
            )

            self.assertIn("NATIVE PROBLEM-INPUT-ONLY CONTRACT", prompt)
            self.assertIn(contract["image_assets"][0]["sha256"], prompt)
            self.assertIn("source_first_without_lean", prompt)
            self.assertIn('"independent_rederivation"', prompt)
            self.assertNotIn("OFFICIAL SOURCE CONTRACT", prompt)
            self.assertNotIn("Blind solve candidate record", prompt)
            self.assertNotIn("Mandatory answer-blind derivation protocol", prompt)
            self.assertNotIn("OLD_CANDIDATE_BIAS_SENTINEL", prompt)
            self.assertIn("measurement_policy", prompt)
            self.assertIn("candidate_domain_policy", prompt)
            source_first_rules = prompt.index(
                "Before opening any generated answer submission"
            )
            generated_input = prompt.index(
                "- Bound generated answer submission"
            )
            self.assertLess(source_first_rules, generated_input)
            normalized_prompt = " ".join(prompt.split())
            for marker in (
                '"Suggest", "propose", or "give a possible"',
                "one source-compatible witness",
                "do not demand or let the candidate claim global uniqueness",
                '"Identify", "draw", or "give the structure"',
                "concrete evidence-supported identification/witness",
                "does not by itself require a finite enumeration of the open chemical universe",
                "global uniqueness theorem",
                '"Determine" or "calculate"',
                'Require global uniqueness only for "unique" or "uniquely"',
                'exhaustive coverage only for "all", "every"',
                "source-only stock-flow ledger",
                "cumulative fresh input",
                "cumulative output",
                "ending inventory",
                "exact denominator",
                "time/cycle horizon",
                "same-initial-cohort interpretation",
                "cumulative-new-feed interpretation",
            ):
                self.assertIn(marker, normalized_prompt)
            source = prompt.index("NATIVE PROBLEM-INPUT-ONLY CONTRACT")
            generated = prompt.index(
                "Treat the current Lean candidate and bound answer submission "
                "as untrusted generated outputs"
            )
            self.assertLess(source, generated)
            self.assertIn("candidate-local `axiom`", prompt)
            self.assertIn("matching dataset_sha256 and record_sha256", prompt)
            self.assertIn(
                "does not establish that the current reaction instantiates",
                " ".join(prompt.split()),
            )
            normalized_chemistry = " ".join(prompt.split())
            for marker in (
                "`contest_interpretation` receipt is not a paper",
                "every required activation cue is bound to an exact problem locator",
                "different-substrate cue fails closed",
                "does not identify the specific reagent",
                "when reagent identity is requested or used decisively",
                "not answer smuggling merely because it is defined as the output carrier",
                "injected into a premise, singleton/answer-shaped domain, opaque predicate",
                "explicit problem arrow or named-final cue is itself the authority",
                "transparent local formula, valence, composition, or topology edits",
                "Never request the directed omitted-protocol rule merely to "
                "authorize this qualitative source-arrow compatibility",
                "Require source-exhaustive candidate-domain provenance only when "
                "a domain is a decisive premise",
                "deterministic preflight passed",
                "seeded import as unsealed",
                "do not fail solely because no global candidate universe was asserted",
                '"staged_species_domain"',
                "quantitative_material_stage",
                "qualitative_named_transform_only",
                "requested conclusion claims a complete stage balance",
                "derivation actually depends on the corresponding species, atom, charge, mass, phase",
                "A requested coefficient or quantity derived directly under a source-stated idealization",
                "Only the conservation dimensions actually used by the conclusion are mandatory",
                "complete combined species/atom/charge/mass/phase ledger only when",
                "non-exclusive compatibility constraint for an identify/draw/give-structure output",
                "Keep omitted protocol details, coefficients, phases, byproducts, and streams unknown",
                "record unrelated omissions as evidence-only limitations",
                "anonymous/catch-all streams or premature terminal-residue reasoning that could change the requested output",
                "not_staged_transformation",
                "Use requested-output materiality as the hard-fail boundary",
                "missing or wrong output/value/unit/branch/scope",
                "vacuous, disconnected carrier",
                "concrete source-compatible countermodel",
                "intended bounded inverse-problem scope",
                "smallest finite domain before filtering",
                "stated or certified-prior constituents",
                "named external inputs",
                "candidate-named singleton",
                "activated target-bound literature within its scope",
                "established ordinary chemical law",
                "invented atom-balanced side reaction or volatile stream",
                "broader generic `fails closed`, bridge-completeness, candidate-domain",
                "source-signaled approximation",
                "source-indicated dominant/slow leg",
                "Missing literature that is not needed for the derivation",
                "evidence-only, not a hard failure",
                "Do not block a bridge or request a dormant rule",
                "A preceding subpart is not automatically a dependency",
                "follow the actual source-stated and Lean dataflow",
                "inner activation-input candidate and answer hash intentionally "
                "belong to the already reviewed parent hop",
                "Different candidate or answer hashes between those two hops "
                "are expected",
            ):
                self.assertIn(marker, normalized_chemistry)
            self.assertIn(
                "bound problem evidence, auditable chemistry evidence allowed "
                "by the bound policy within its exact scope",
                normalized_chemistry,
            )
            self.assertIn(
                "provenance for an output-decisive domain, or why no domain is decisive",
                normalized_chemistry,
            )

            blueprint_schema = next(
                line.strip() for line in prompt.splitlines()
                if '"blueprint_conflicts"' in line
            )
            self.assertIn(
                '"blueprint_conflicts": [{"source_claim":"...",'
                '"blueprint_or_lean_claim":"...","status":'
                '"resolved_in_favor_of_problem_source|unresolved|failed",'
                '"evidence":"..."}]',
                blueprint_schema,
            )
            for alias in ("carrier", "claim", "conflict", "lean_claim"):
                self.assertNotIn(f'"{alias}"', blueprint_schema)
            self.assertIn(
                "`blueprint_conflicts` may be `[]` only when there is no "
                "source conflict",
                prompt,
            )

    def test_native_target_worker_certificate_uses_semantic_validator(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target, contract = _native_project(root)
            rel = target.relative_to(root).as_posix()
            path = root / "milestones.jsonl"
            milestone = _milestone(rel)
            milestone["formalization_review"]["independent_rederivation"] = (
                build_independent_rederivation_example(contract)
            )
            path.write_text(json.dumps(milestone) + "\n")

            row, error = load_target_formalization_milestone(
                path, rel, None, contract,
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(row)

            milestone["formalization_review"]["independent_rederivation"][
                "requested_outputs"
            ][0]["lean_statement_comparison"]["status"] = "mismatched"
            path.write_text(json.dumps(milestone) + "\n")
            row, error = load_target_formalization_milestone(
                path, rel, None, contract,
            )
            self.assertIsNone(row)
            self.assertIn("must be matched", error)

    def test_r10_r11_schema_feedback_reaches_attempt_two_and_stays_schema_only(self):
        cases = (
            (
                "missing_unit",
                "independent_rederivation.requested_outputs[0].constants[0]",
                '"unit"',
            ),
            (
                "unsupported_scope",
                "independent_rederivation.requested_outputs[0].process_scope.kind",
                '"overall"',
            ),
            (
                "extra_role",
                "independent_rederivation.requested_outputs[0].constants[0]",
                '"source_locator"',
            ),
            (
                "unsupported_dependency",
                "independent_rederivation.requested_outputs[0].dependencies[0].kind",
                '"governing_relation"',
            ),
        )
        for defect, expected_path, expected_contract in cases:
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                target, contract = _native_project(root)
                rel = target.relative_to(root).as_posix()
                state = root / ".archon"
                iter_dir = state / "logs/iter-010"
                iter_dir.mkdir(parents=True)
                prompts: list[str] = []
                invalid = _r10_invalid_native_milestone(rel, contract, defect)

                def forbidden_executor(**_kwargs):
                    self.fail("single-target Review must not instantiate an executor")

                def schema_then_success(spec, **_kwargs):
                    prompts.append(spec.prompt)
                    if spec.attempt == 1:
                        output_dir = Path(spec.output_dir)
                        output_dir.mkdir(parents=True, exist_ok=True)
                        (output_dir / "milestones.jsonl").write_text(
                            json.dumps(invalid) + "\n",
                            encoding="utf-8",
                        )
                        return TargetReviewOutcome(
                            rel=spec.rel,
                            attempt=spec.attempt,
                            runner_ok=True,
                            milestone=None,
                            error=(
                                "TRANSPORT_TEXT_MUST_NOT_BE_FEEDBACK "
                                "OFFICIAL_ANSWER_SENTINEL"
                            ),
                        )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=_native_milestone(spec.rel, contract),
                    )

                report = run_parallel_formalization_reviews(
                    project_path=root,
                    state_dir=state,
                    iter_dir=iter_dir,
                    iter_num=10,
                    objectives=[target],
                    preflight={
                        "targets": [_native_preflight(root, rel)],
                    },
                    prior_gate_targets={},
                    requested_jobs=8,
                    max_attempts=2,
                    backoff_sec=0,
                    verbose_logs=False,
                    model=None,
                    backend=None,
                    harness=None,
                    worker_fn=schema_then_success,
                    executor_factory=forbidden_executor,
                    sleep_fn=lambda _seconds: None,
                )

                self.assertTrue(report["complete"])
                self.assertEqual(len(prompts), 2)
                self.assertNotIn("CONTROLLER STRUCTURAL SCHEMA FEEDBACK", prompts[0])
                marker, separator, feedback = prompts[1].partition(
                    "CONTROLLER STRUCTURAL SCHEMA FEEDBACK"
                )
                self.assertTrue(separator)
                self.assertTrue(marker)
                self.assertIn(expected_path, feedback)
                self.assertIn(expected_contract, feedback)
                self.assertIn("one complete milestone JSONL row", feedback)
                self.assertIn("full formalization_review certificate", feedback)
                payload = next(
                    line for line in feedback.splitlines()
                    if line.startswith("{")
                )
                self.assertLessEqual(len(payload.encode("ascii")), 2_048)
                self.assertTrue(all(ord(character) >= 0x20 for character in payload))
                self.assertNotIn("OFFICIAL_ANSWER_SENTINEL", feedback)
                self.assertNotIn("PRIOR_DERIVATION_SENTINEL", feedback)
                self.assertNotIn("TRANSPORT_TEXT_MUST_NOT_BE_FEEDBACK", feedback)

    def test_blueprint_conflict_retry_feedback_projects_full_schema_only(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target, contract = _native_project(root)
            rel = target.relative_to(root).as_posix()
            state = root / ".archon"
            iter_dir = state / "logs/iter-012"
            iter_dir.mkdir(parents=True)
            prompts: list[str] = []
            rejected = {
                "formalization_review": {
                    "blueprint_conflicts": [{
                        "carrier": "RAW_CARRIER_SENTINEL",
                        "claim": (
                            "RAW_CLAIM_SENTINEL "
                            "https://attacker.invalid/answer"
                        ),
                        "evidence": "EXPECTED_ANSWER_SENTINEL",
                    }],
                },
            }

            def forbidden_executor(**_kwargs):
                self.fail("single-target Review must not instantiate an executor")

            def schema_then_success(spec, **_kwargs):
                prompts.append(spec.prompt)
                if spec.attempt == 1:
                    output_dir = Path(spec.output_dir)
                    output_dir.mkdir(parents=True, exist_ok=True)
                    (output_dir / "milestones.jsonl").write_text(
                        json.dumps(rejected) + "\n",
                        encoding="utf-8",
                    )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=None,
                        error="RAW_TRANSPORT_SENTINEL",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_native_milestone(spec.rel, contract),
                )

            with mock.patch.object(
                parallel_formalization_review,
                "load_target_formalization_milestone",
                return_value=(
                    None,
                    "blueprint conflict 1 is missing source_claim",
                ),
            ):
                report = run_parallel_formalization_reviews(
                    project_path=root,
                    state_dir=state,
                    iter_dir=iter_dir,
                    iter_num=12,
                    objectives=[target],
                    preflight={"targets": [_native_preflight(root, rel)]},
                    prior_gate_targets={},
                    requested_jobs=4,
                    max_attempts=2,
                    backoff_sec=0,
                    verbose_logs=False,
                    model=None,
                    backend=None,
                    harness=None,
                    worker_fn=schema_then_success,
                    executor_factory=forbidden_executor,
                    sleep_fn=lambda _seconds: None,
                )

            self.assertTrue(report["complete"])
            self.assertEqual(len(prompts), 2)
            feedback = prompts[1].partition(
                "CONTROLLER STRUCTURAL SCHEMA FEEDBACK"
            )[2]
            payload = json.loads(next(
                line for line in feedback.splitlines()
                if line.startswith("{")
            ))
            item = payload["feedback_history"][0]
            self.assertEqual(
                item["required_exact_keys"],
                ["blueprint_or_lean_claim", "evidence", "source_claim", "status"],
            )
            self.assertEqual(
                item["enum_constraints"]["status"],
                ["failed", "resolved_in_favor_of_problem_source", "unresolved"],
            )
            for sentinel in (
                "RAW_CARRIER_SENTINEL",
                "RAW_CLAIM_SENTINEL",
                "EXPECTED_ANSWER_SENTINEL",
                "RAW_TRANSPORT_SENTINEL",
                "attacker.invalid",
            ):
                self.assertNotIn(sentinel, feedback)

    def test_schema_feedback_accumulates_attempt_three_but_transport_cannot_create_it(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target, contract = _native_project(root)
            rel = target.relative_to(root).as_posix()
            state = root / ".archon"
            iter_dir = state / "logs/iter-011"
            iter_dir.mkdir(parents=True)
            prompts: list[str] = []

            def forbidden_executor(**_kwargs):
                self.fail("single-target Review must not instantiate an executor")

            def two_schema_failures_then_success(spec, **_kwargs):
                prompts.append(spec.prompt)
                if spec.attempt < 3:
                    defect = (
                        "missing_unit"
                        if spec.attempt == 1
                        else "unsupported_dependency"
                    )
                    invalid = _r10_invalid_native_milestone(
                        spec.rel, contract, defect,
                    )
                    output_dir = Path(spec.output_dir)
                    output_dir.mkdir(parents=True, exist_ok=True)
                    (output_dir / "milestones.jsonl").write_text(
                        json.dumps(invalid) + "\n",
                        encoding="utf-8",
                    )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=None,
                        error="untrusted worker text is ignored",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_native_milestone(spec.rel, contract),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=11,
                objectives=[target],
                preflight={"targets": [_native_preflight(root, rel)]},
                prior_gate_targets={},
                requested_jobs=4,
                max_attempts=3,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=two_schema_failures_then_success,
                executor_factory=forbidden_executor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(len(prompts), 3)
            feedback_two = prompts[1].partition(
                "CONTROLLER STRUCTURAL SCHEMA FEEDBACK"
            )[2]
            feedback_three = prompts[2].partition(
                "CONTROLLER STRUCTURAL SCHEMA FEEDBACK"
            )[2]
            self.assertIn('"required_exact_keys"', feedback_two)
            self.assertNotIn('"allowed_values"', feedback_two)
            self.assertIn('"required_exact_keys"', feedback_three)
            self.assertIn('"allowed_values"', feedback_three)
            self.assertIn("dependencies[0].kind", feedback_three)
            self.assertNotIn("OFFICIAL_ANSWER_SENTINEL", feedback_three)

            transport_state = root / ".archon-transport"
            transport_iter = transport_state / "logs/iter-012"
            transport_iter.mkdir(parents=True)
            transport_prompts: list[str] = []

            def transport_then_success(spec, **_kwargs):
                transport_prompts.append(spec.prompt)
                if spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=False,
                        milestone=None,
                        error=(
                            "independent_rederivation.requested_outputs[0] "
                            "has invalid fields: missing unit; "
                            "OFFICIAL_ANSWER_SENTINEL"
                        ),
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_native_milestone(spec.rel, contract),
                )

            transport_report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=transport_state,
                iter_dir=transport_iter,
                iter_num=12,
                objectives=[target],
                preflight={"targets": [_native_preflight(root, rel)]},
                prior_gate_targets={},
                requested_jobs=4,
                max_attempts=2,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=transport_then_success,
                executor_factory=forbidden_executor,
                sleep_fn=lambda _seconds: None,
            )
            self.assertTrue(transport_report["complete"])
            self.assertEqual(len(transport_prompts), 2)
            self.assertNotIn(
                "CONTROLLER STRUCTURAL SCHEMA FEEDBACK",
                transport_prompts[1],
            )
            self.assertNotIn("OFFICIAL_ANSWER_SENTINEL", transport_prompts[1])
            self.assertNotIn(
                "has invalid fields: missing unit",
                transport_prompts[1],
            )

    def test_previous_then_pinned_feedback_is_deduplicated_and_accumulated(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target, contract = _native_project(root)
            rel = target.relative_to(root).as_posix()
            state = root / ".archon"
            iter_dir = state / "logs/iter-014"
            iter_dir.mkdir(parents=True)
            prompts: list[str] = []

            def forbidden_executor(**_kwargs):
                self.fail("single-target Review must not instantiate an executor")

            def previous_then_pinned_then_success(spec, **_kwargs):
                prompts.append(spec.prompt)
                if spec.attempt < 3:
                    invalid = _native_milestone(spec.rel, contract)
                    output = invalid["formalization_review"][
                        "independent_rederivation"
                    ]["requested_outputs"][0]
                    if spec.attempt == 1:
                        output["source_locators"] = [{
                            "kind": "previous_parts",
                            "reference": "999",
                        }]
                    else:
                        output["source_locators"] = [{
                            "kind": "pinned_library",
                            "reference": "Project.Local.secret",
                        }]
                    output_dir = Path(spec.output_dir)
                    output_dir.mkdir(parents=True, exist_ok=True)
                    (output_dir / "milestones.jsonl").write_text(
                        json.dumps(invalid) + "\n",
                        encoding="utf-8",
                    )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=None,
                        error="UNTRUSTED_RAW_LOCATOR_SENTINEL",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_native_milestone(spec.rel, contract),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=14,
                objectives=[target],
                preflight={"targets": [_native_preflight(root, rel)]},
                prior_gate_targets={},
                requested_jobs=4,
                max_attempts=3,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=previous_then_pinned_then_success,
                executor_factory=forbidden_executor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(len(prompts), 3)
            self.assertNotIn("STRUCTURAL SCHEMA FEEDBACK", prompts[0])
            self.assertIn(
                "certified_prior_result.producers[existing_index]."
                "typed_exports[existing_index]", prompts[1],
            )
            self.assertNotIn(
                "safe fully-qualified existing declaration", prompts[1],
            )
            self.assertIn(
                "certified_prior_result.producers[existing_index]."
                "typed_exports[existing_index]", prompts[2],
            )
            self.assertIn(
                "safe fully-qualified existing declaration", prompts[2],
            )
            self.assertEqual(
                prompts[2].count("CONTROLLER STRUCTURAL SCHEMA FEEDBACK"), 1,
            )
            self.assertNotIn("Project.Local.secret", prompts[2])
            self.assertNotIn("UNTRUSTED_RAW_LOCATOR_SENTINEL", prompts[2])

        base = {
            "error_kind": "schema_validation",
            "issue": "wrong_type",
            "field_path": "independent_rederivation.requested_outputs[0].id",
            "expected_type": "string",
        }
        history = parallel_formalization_review._extend_schema_feedback_history(
            [], base,
        )
        history = parallel_formalization_review._extend_schema_feedback_history(
            history, dict(base),
        )
        self.assertEqual(len(history), 1)
        for index in range(10):
            item = dict(base)
            item["field_path"] = (
                f"independent_rederivation.requested_outputs[{index}].id"
            )
            history = parallel_formalization_review._extend_schema_feedback_history(
                history, item,
            )
        self.assertLessEqual(len(history), 4)
        rendered = parallel_formalization_review._append_schema_retry_feedback(
            "base", history,
        )
        payload = next(
            line for line in rendered.splitlines()
            if line.startswith('{"feedback_history"')
        )
        self.assertLessEqual(len(payload.encode("ascii")), 2_048)
        self.assertTrue(all(ord(character) >= 0x20 for character in payload))

    def test_loaded_native_milestone_rejects_previous_part_as_a_conclusion(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target, contract = _native_project(root)
            contract["previous_parts_count"] = 1
            contract["problem_evidence"]["previous_parts"] = [{
                "question": "trusted prior question",
            }]
            rel = target.relative_to(root).as_posix()
            milestone = _native_milestone(rel, contract)
            milestone["formalization_review"]["independent_rederivation"][
                "requested_outputs"
            ][0]["source_locators"] = [{
                "kind": "previous_parts",
                "reference": "0",
            }]
            path = root / "milestones.jsonl"
            path.write_text(json.dumps(milestone) + "\n", encoding="utf-8")

            loaded, error = load_target_formalization_milestone(
                path, rel, None, contract,
            )

            self.assertIn(
                "uncertified previous_parts conclusion", error,
            )
            self.assertIsNone(loaded)

    def test_transport_failure_preserves_prior_safe_feedback(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target, contract = _native_project(root)
            rel = target.relative_to(root).as_posix()
            state = root / ".archon"
            iter_dir = state / "logs/iter-015"
            iter_dir.mkdir(parents=True)
            prompts: list[str] = []

            def worker(spec, **_kwargs):
                prompts.append(spec.prompt)
                if spec.attempt == 1:
                    invalid = _r10_invalid_native_milestone(
                        spec.rel, contract, "missing_unit",
                    )
                    output_dir = Path(spec.output_dir)
                    output_dir.mkdir(parents=True, exist_ok=True)
                    (output_dir / "milestones.jsonl").write_text(
                        json.dumps(invalid) + "\n", encoding="utf-8",
                    )
                    return TargetReviewOutcome(
                        rel=spec.rel, attempt=1, runner_ok=True,
                        milestone=None, error="RAW_ONE",
                    )
                if spec.attempt == 2:
                    return TargetReviewOutcome(
                        rel=spec.rel, attempt=2, runner_ok=False,
                        milestone=None, error="RAW_TRANSPORT_SENTINEL",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel, attempt=3, runner_ok=True,
                    milestone=_native_milestone(spec.rel, contract),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=15,
                objectives=[target],
                preflight={"targets": [_native_preflight(root, rel)]},
                prior_gate_targets={},
                requested_jobs=1,
                max_attempts=3,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=worker,
                executor_factory=lambda **_kwargs: None,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertIn('"required_exact_keys"', prompts[1])
            self.assertIn('"required_exact_keys"', prompts[2])
            self.assertNotIn("RAW_TRANSPORT_SENTINEL", prompts[2])

    def test_r12_locator_and_size_failures_receive_safe_retry_feedback(self):
        cases = (
            ("problem_text", "exact scalar root[#safe-fragment]"),
            (
                "previous_parts",
                "ASCII decimal zero-based index or previous_parts[index][.field]",
            ),
            ("output_size", '"max_bytes":8192'),
        )
        for defect, expected_feedback in cases:
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                target, contract = _native_project(root)
                rel = target.relative_to(root).as_posix()
                state = root / ".archon"
                iter_dir = state / "logs/iter-012-r12"
                iter_dir.mkdir(parents=True)
                prompts: list[str] = []
                invalid = _native_milestone(rel, contract)
                output = invalid["formalization_review"][
                    "independent_rederivation"
                ]["requested_outputs"][0]
                if defect == "problem_text":
                    output["constants"] = [{
                        "name": "source factor",
                        "value": 1,
                        "unit": "dimensionless",
                        "source_locator": {
                            "kind": "problem_text",
                            "reference": "OFFICIAL_ANSWER_SENTINEL",
                        },
                    }]
                elif defect == "previous_parts":
                    output["dependencies"] = [{
                        "kind": "previous_part",
                        "reference": "source relation",
                        "relation": "use the problem-only prior relation",
                        "source_locator": {
                            "kind": "previous_parts",
                            "reference": "previous_parts[999].OFFICIAL_ANSWER_SENTINEL",
                        },
                    }]
                elif defect == "output_size":
                    output["evidence"] = "OFFICIAL_ANSWER_SENTINEL" * 400
                else:  # pragma: no cover - guarded by the static cases above
                    raise AssertionError(defect)

                def forbidden_executor(**_kwargs):
                    self.fail("single-target Review must not instantiate an executor")

                def invalid_then_success(spec, **_kwargs):
                    prompts.append(spec.prompt)
                    if spec.attempt == 1:
                        output_dir = Path(spec.output_dir)
                        output_dir.mkdir(parents=True, exist_ok=True)
                        (output_dir / "milestones.jsonl").write_text(
                            json.dumps(invalid) + "\n",
                            encoding="utf-8",
                        )
                        return TargetReviewOutcome(
                            rel=spec.rel,
                            attempt=spec.attempt,
                            runner_ok=True,
                            milestone=None,
                            error="UNTRUSTED_RAW_ERROR_OFFICIAL_ANSWER_SENTINEL",
                        )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=_native_milestone(spec.rel, contract),
                    )

                report = run_parallel_formalization_reviews(
                    project_path=root,
                    state_dir=state,
                    iter_dir=iter_dir,
                    iter_num=12,
                    objectives=[target],
                    preflight={"targets": [_native_preflight(root, rel)]},
                    prior_gate_targets={},
                    requested_jobs=4,
                    max_attempts=2,
                    backoff_sec=0,
                    verbose_logs=False,
                    model=None,
                    backend=None,
                    harness=None,
                    worker_fn=invalid_then_success,
                    executor_factory=forbidden_executor,
                    sleep_fn=lambda _seconds: None,
                )

                self.assertTrue(report["complete"])
                self.assertEqual(len(prompts), 2)
                self.assertNotIn(
                    "CONTROLLER STRUCTURAL SCHEMA FEEDBACK", prompts[0],
                )
                self.assertIn("CONTROLLER STRUCTURAL SCHEMA FEEDBACK", prompts[1])
                self.assertIn(expected_feedback, prompts[1])
                self.assertNotIn("OFFICIAL_ANSWER_SENTINEL", prompts[1])
                self.assertNotIn("UNTRUSTED_RAW_ERROR", prompts[1])

    def test_schema_feedback_is_target_isolated_in_multi_target_retries(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target_contracts = _native_project_pair(root)
            contracts = {
                target.relative_to(root).as_posix(): contract
                for target, contract in target_contracts
            }
            targets = [target for target, _contract in target_contracts]
            rels = sorted(contracts)
            schema_rel, semantic_rel = rels
            state = root / ".archon"
            iter_dir = state / "logs/iter-013"
            iter_dir.mkdir(parents=True)
            prompts: dict[str, list[str]] = {rel: [] for rel in rels}
            executor_workers: list[int] = []

            def tracking_executor(*, max_workers):
                executor_workers.append(max_workers)
                return ThreadPoolExecutor(max_workers=max_workers)

            def isolated_retry_worker(spec, **_kwargs):
                prompts[spec.rel].append(spec.prompt)
                if spec.attempt == 1 and spec.rel == schema_rel:
                    invalid = _r10_invalid_native_milestone(
                        spec.rel,
                        contracts[spec.rel],
                        "unsupported_dependency",
                    )
                    output_dir = Path(spec.output_dir)
                    output_dir.mkdir(parents=True, exist_ok=True)
                    (output_dir / "milestones.jsonl").write_text(
                        json.dumps(invalid) + "\n",
                        encoding="utf-8",
                    )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=None,
                        error="SCHEMA_TARGET_RAW_ERROR_SENTINEL",
                    )
                if spec.attempt == 1:
                    invalid = _native_milestone(spec.rel, contracts[spec.rel])
                    invalid["formalization_review"]["independent_rederivation"][
                        "requested_outputs"
                    ][0]["unit"] = "SEMANTIC_VALUE_SENTINEL"
                    output_dir = Path(spec.output_dir)
                    output_dir.mkdir(parents=True, exist_ok=True)
                    (output_dir / "milestones.jsonl").write_text(
                        json.dumps(invalid) + "\n",
                        encoding="utf-8",
                    )
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=None,
                        error=(
                            "dependencies[0].kind is unsupported; "
                            "FORGED_RAW_ERROR_SENTINEL"
                        ),
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_native_milestone(spec.rel, contracts[spec.rel]),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=13,
                objectives=targets,
                preflight={"targets": [
                    _native_preflight(root, rel) for rel in rels
                ]},
                prior_gate_targets={},
                requested_jobs=2,
                max_attempts=2,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=isolated_retry_worker,
                executor_factory=tracking_executor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(executor_workers, [2, 1])
            self.assertEqual([len(prompts[rel]) for rel in rels], [2, 2])
            self.assertIn(
                "CONTROLLER STRUCTURAL SCHEMA FEEDBACK",
                prompts[schema_rel][1],
            )
            self.assertIn("dependencies[0].kind", prompts[schema_rel][1])
            self.assertNotIn(
                "SCHEMA_TARGET_RAW_ERROR_SENTINEL", prompts[schema_rel][1],
            )
            self.assertNotIn(
                "CONTROLLER STRUCTURAL SCHEMA FEEDBACK",
                prompts[semantic_rel][1],
            )
            self.assertNotIn(
                "SEMANTIC_VALUE_SENTINEL", prompts[semantic_rel][1],
            )
            self.assertNotIn(
                "FORGED_RAW_ERROR_SENTINEL", prompts[semantic_rel][1],
            )
            self.assertNotIn("dependencies[0].kind", prompts[semantic_rel][1])

    def test_blind_prompt_uses_blind_schema_and_freeze_protocol(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            target = root / "Problems" / "A.lean"
            target.parent.mkdir(parents=True)
            target.write_text("theorem a : True := by sorry\n")
            prompt = build_target_formalization_review_prompt(
                project_path=root,
                state_dir=root / ".archon",
                iter_dir=root / ".archon" / "iter-1",
                iter_num=1,
                target=target,
                output_dir=root / ".archon" / "review",
                preflight={"compiles": True},
                prior_gate_record=None,
                source_contract=_blind_contract("Problems/A.lean"),
            )
            self.assertIn("Mandatory answer-blind derivation protocol", prompt)
            self.assertIn("symbolic specification", prompt)
            self.assertIn("frozen before any later reveal", prompt)
            for name in (
                "answer_independence", "raw_derivation",
                "reporting_rule_source", "tolerance_provenance",
                "candidate_domain_provenance", "lean_result_binding",
            ):
                self.assertIn(name, prompt)
            normalized_prompt = " ".join(prompt.split())
            for marker in (
                "one current semantic snapshot",
                "pre-redraft snapshot",
                "block it as `needs_redraft`",
                "Internally self-consistent candidate hashes do not excuse",
                "Do not repair the candidate yourself",
            ):
                self.assertIn(marker, normalized_prompt)
            for marker in (
                "source-first arrow certificate",
                "state the arrowhead\ndirection",
                "enumerate all precursors at the tail",
                "identify the product at the head",
                "trace a\ndistinctive scaffold or motif",
                "Cross-check\nthat scaffold against every adjacent product",
                "expand every chemical abbreviation",
                "terminal or capping group",
                "complete elemental formula",
                "Mark its\nattachment boundary",
                "count\nevery atom exactly once",
            ):
                self.assertIn(marker, prompt)
            self.assertNotIn('"official_answer_alignment"', prompt)
            self.assertNotIn('"source_inconsistency"', prompt)

    def test_prompt_is_target_scoped_and_allows_sorry_bodies(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            target = root / "Problems" / "A.lean"
            output = (
                iter_dir / "formalization-review-targets" / "Problems_A"
                / "attempt-1"
            )
            target.parent.mkdir(parents=True)
            result_dir = state / "task_results"
            result_dir.mkdir(parents=True)
            flat_result = result_dir / "A.md"
            flat_result.write_text("current formalizer result\n")
            target.write_text("theorem a : True := by sorry\n")

            prompt = build_target_formalization_review_prompt(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=1,
                target=target,
                output_dir=output,
                preflight={"file": "Problems/A.lean", "compiles": True},
                prior_gate_record=None,
            )

            self.assertIn("Assigned target (review only this target)", prompt)
            self.assertIn("semantic formalization Review", prompt)
            self.assertIn("`sorry` proof bodies are", prompt)
            self.assertIn("Do not edit", prompt)
            self.assertIn("PROGRESS.md", prompt)
            self.assertIn(str(output / "milestones.jsonl"), prompt)
            self.assertIn("countermodel_resistance", prompt)
            normalized_prompt = " ".join(prompt.split())
            for marker in (
                "Use requested-output materiality as the hard-fail boundary",
                "missing or wrong output/value/unit/branch/scope",
                "source-indicated dominant/slow leg",
                "Missing literature that is not needed for the derivation",
                "complete combined species/atom/charge/mass/phase ledger only when",
            ):
                self.assertIn(marker, normalized_prompt)

            self.assertIn(str(flat_result), prompt)

    def test_certificate_validation_is_target_strict_and_fail_closed(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "milestones.jsonl"
            path.write_text(json.dumps(_milestone("A.lean")) + "\n")

            row, error = load_target_formalization_milestone(path, "A.lean")
            self.assertEqual(row["status"], "solved")
            self.assertEqual(error, "")

            row, error = load_target_formalization_milestone(path, "B.lean")
            self.assertIsNone(row)
            self.assertIn("!=", error)

            contradictory = _milestone("A.lean")
            contradictory["formalization_review"]["checks"][
                "source_faithfulness"
            ]["status"] = "failed"
            path.write_text(json.dumps(contradictory) + "\n")
            row, error = load_target_formalization_milestone(path, "A.lean")
            self.assertIsNone(row)
            self.assertIn("contradicts", error)

    def test_single_target_runs_synchronously_without_executor(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-001"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n")

            def forbidden_executor(**_kwargs):
                self.fail("single-target Review must not instantiate an executor")

            def successful_worker(spec, **_kwargs):
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=1,
                objectives=[target],
                preflight={"targets": [{"file": target.name, "compiles": True}]},
                prior_gate_targets={},
                requested_jobs=8,
                max_attempts=1,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=successful_worker,
                executor_factory=forbidden_executor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(report["reviewed"], 1)
            self.assertEqual(report["rounds"], [{
                "attempt": 1,
                "jobs": 1,
                "submitted": 1,
                "completed": 1,
                "failed": 0,
            }])

    def test_single_target_worker_exception_uses_normal_retry_path(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-002"
            iter_dir.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n")
            attempts: list[int] = []
            sleeps: list[float] = []

            def forbidden_executor(**_kwargs):
                self.fail("single-target retry must not instantiate an executor")

            def transient_worker(spec, **_kwargs):
                attempts.append(spec.attempt)
                if spec.attempt == 1:
                    raise RuntimeError("transient worker failure")
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=2,
                objectives=[target],
                preflight={"targets": [{"file": target.name, "compiles": True}]},
                prior_gate_targets={},
                requested_jobs=8,
                max_attempts=2,
                backoff_sec=0.25,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=transient_worker,
                executor_factory=forbidden_executor,
                sleep_fn=sleeps.append,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(attempts, [1, 2])
            self.assertEqual(sleeps, [0.25])
            self.assertEqual(
                [(item["jobs"], item["failed"]) for item in report["rounds"]],
                [(1, 1), (1, 0)],
            )

    def test_multiple_targets_still_use_executor_after_backoff_to_one_job(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-003"
            iter_dir.mkdir(parents=True)
            targets = []
            for name in ("A.lean", "B.lean"):
                target = root / name
                target.write_text("theorem a : True := by sorry\n")
                targets.append(target)

            calls: list[tuple[str, int]] = []
            executor_workers: list[int] = []

            def tracking_executor(*, max_workers):
                executor_workers.append(max_workers)
                return ThreadPoolExecutor(max_workers=max_workers)

            def transient_worker(spec, **_kwargs):
                calls.append((spec.rel, spec.attempt))
                if spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=False,
                        milestone=None,
                        error="retry",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(spec.rel),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=3,
                objectives=targets,
                preflight={
                    "targets": [
                        {"file": target.name, "compiles": True}
                        for target in targets
                    ],
                },
                prior_gate_targets={},
                requested_jobs=2,
                max_attempts=2,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=transient_worker,
                executor_factory=tracking_executor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(report["reviewed"], 2)
            self.assertEqual(report["unresolved"], [])
            self.assertEqual(executor_workers, [2, 1])
            self.assertEqual(
                sorted(calls),
                [
                    ("A.lean", 1), ("A.lean", 2),
                    ("B.lean", 1), ("B.lean", 2),
                ],
            )
            self.assertEqual(
                [(item["jobs"], item["failed"]) for item in report["rounds"]],
                [(2, 2), (1, 0)],
            )

    def test_transient_failures_halve_concurrency_then_merge_once(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-002"
            iter_dir.mkdir(parents=True)
            objectives = []
            for name in ("A", "B", "C", "D"):
                target = root / f"{name}.lean"
                target.write_text(f"theorem {name.lower()} : True := by sorry\n")
                objectives.append(target)

            calls: dict[str, int] = {}
            executor_workers: list[int] = []

            def tracking_executor(*, max_workers):
                executor_workers.append(max_workers)
                return ThreadPoolExecutor(max_workers=max_workers)
            prompts: dict[tuple[str, int], str] = {}
            validation_error = (
                "source_contract does not match native problem-only evidence: "
                "source_record_sha256 actual length 60, expected 64"
            )

            def fake_worker(spec, **_kwargs):
                calls[spec.rel] = calls.get(spec.rel, 0) + 1
                prompts[(spec.rel, spec.attempt)] = spec.prompt
                if spec.rel == "B.lean" and spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=True,
                        milestone=None,
                        error=validation_error,
                        validation_error=validation_error,
                    )
                if spec.rel == "D.lean" and spec.attempt == 1:
                    return TargetReviewOutcome(
                        rel=spec.rel,
                        attempt=spec.attempt,
                        runner_ok=False,
                        milestone=None,
                        error="429 rate limit",
                    )
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=True,
                    milestone=_milestone(
                        spec.rel, passed=spec.rel != "D.lean",
                    ),
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=2,
                objectives=objectives,
                preflight={"targets": [
                    {"file": path.name, "compiles": True}
                    for path in objectives
                ]},
                prior_gate_targets={},
                requested_jobs=4,
                max_attempts=3,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=fake_worker,
                executor_factory=tracking_executor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertTrue(report["complete"])
            self.assertEqual(executor_workers, [4, 2])
            self.assertEqual(
                [(item["jobs"], item["failed"]) for item in report["rounds"]],
                [(4, 2), (2, 0)],
            )
            self.assertEqual(calls, {
                "A.lean": 1,
                "B.lean": 2,
                "C.lean": 1,
                "D.lean": 2,
            })
            self.assertNotIn(validation_error, prompts[("B.lean", 1)])
            self.assertIn(validation_error, prompts[("B.lean", 2)])
            self.assertIn(
                "CONTROLLER SEALED-VALIDATOR RETRY FEEDBACK",
                prompts[("B.lean", 2)],
            )
            self.assertNotIn(validation_error, prompts[("D.lean", 2)])
            session = state / "proof-journal" / "sessions" / "session_2"
            rows = [
                json.loads(line)
                for line in (session / "milestones.jsonl").read_text().splitlines()
            ]
            self.assertEqual(
                [row["target"]["file"] for row in rows],
                ["A.lean", "B.lean", "C.lean", "D.lean"],
            )
            self.assertIn(
                "D.lean",
                (session / "recommendations.md").read_text(),
            )

    def test_incomplete_batch_does_not_replace_existing_session(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-003"
            session = state / "proof-journal" / "sessions" / "session_3"
            iter_dir.mkdir(parents=True)
            session.mkdir(parents=True)
            target = root / "A.lean"
            target.write_text("theorem a : True := by sorry\n")
            milestone_path = session / "milestones.jsonl"
            milestone_path.write_text("preexisting journal\n")

            def failed_worker(spec, **_kwargs):
                return TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=spec.attempt,
                    runner_ok=False,
                    milestone=None,
                    error="malformed output",
                )

            report = run_parallel_formalization_reviews(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=3,
                objectives=[target],
                preflight={"targets": []},
                prior_gate_targets={},
                requested_jobs=2,
                max_attempts=1,
                backoff_sec=0,
                verbose_logs=False,
                model=None,
                backend=None,
                harness=None,
                worker_fn=failed_worker,
                executor_factory=ThreadPoolExecutor,
                sleep_fn=lambda _seconds: None,
            )

            self.assertFalse(report["complete"])
            self.assertEqual(report["unresolved"], ["A.lean"])
            self.assertEqual(milestone_path.read_text(), "preexisting journal\n")


if __name__ == "__main__":
    unittest.main()
