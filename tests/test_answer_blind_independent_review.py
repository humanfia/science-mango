from __future__ import annotations

import importlib.util
import json
import os
import shutil
import stat
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_answer_blind_independent_review.py"
sys.path.insert(0, str(ROOT / "src"))
SPEC = importlib.util.spec_from_file_location("answer_blind_independent_review", SCRIPT)
assert SPEC and SPEC.loader
REVIEW = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = REVIEW
SPEC.loader.exec_module(REVIEW)


def _write(path: Path, value: object, *, mode: int = 0o400) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(REVIEW._pretty(value))
    os.chown(path, 0, 0)
    os.chmod(path, mode)


@unittest.skipUnless(os.geteuid() == 0, "structured Review controller is root-only")
class StructuredIndependentReviewTests(unittest.TestCase):
    def setUp(self) -> None:
        self.base = Path(tempfile.mkdtemp(prefix="answer-blind-review-", dir="/var/lib"))
        os.chown(self.base, 0, 0)
        os.chmod(self.base, 0o755)
        self.workspace = self.base / "workspace"
        self.controller = self.base / "controller"
        self.assets = self.base / "assets"
        self.dependency = self.base / "dependency"
        for path, mode in (
            (self.workspace, 0o755), (self.controller, 0o700),
            (self.assets, 0o755), (self.dependency, 0o755),
            (self.workspace / ".archon", 0o755),
        ):
            path.mkdir(parents=True, exist_ok=True)
            os.chown(path, 0, 0)
            os.chmod(path, mode)
        self.record_id = "icho_2026_t1_a1"
        self.run_id = "review-unit-run"
        self.image = self.assets / "page.png"
        self.image.write_bytes(b"problem-page")
        os.chown(self.image, 0, 0)
        os.chmod(self.image, 0o400)
        self.row = {
            "schema_version": 1, "protocol": REVIEW.PROTOCOL,
            "evaluation_mode": "answer_blind", "official_answer_seen": False,
            "phase": "solve", "id": self.record_id,
            "question": "Compute the printed quantity.",
            "current_question": "Compute the printed quantity.",
            "shared_context": "Use only the printed data.", "previous_parts": [],
            "images": ["page.png"],
            "problem_assets": [{
                "kind": "problem_page", "path": "page.png",
                "sha256": REVIEW._file_sha(self.image),
            }],
            "requested_outputs": [{
                "id": "result", "source_requirement": "printed quantity",
                "kind": "numeric", "unit": "mol",
                "reporting_policy": {
                    "kind": "decimal_places", "digits": 2,
                    "tie_rule": "half_away_from_zero",
                },
            }],
            "reporting_policy": {
                "intermediate_rounding": "forbidden",
                "final_precision": {"kind": "decimal_places", "digits": 2},
                "tie_rule": "half_away_from_zero",
            },
            "measurement_policy": {"derived_tolerances": "prove from inputs"},
            "candidate_domain_policy": {"allowed_sources": ["problem_text"]},
        }
        self.bundle = self.base / "questions.jsonl"
        self.bundle.write_bytes(REVIEW._canonical(self.row))
        os.chown(self.bundle, 0, 0)
        os.chmod(self.bundle, 0o400)
        for relative in REVIEW.ROOT_GENERATED:
            path = self.workspace / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"trusted {relative}\n", encoding="utf-8")
            os.chown(path, 0, 0)
            os.chmod(path, 0o400)
        seed_payload = self.workspace / "IChO2026Chem.lean"
        seed_payload.write_text("namespace IChO2026Chem\nend IChO2026Chem\n", encoding="utf-8")
        os.chown(seed_payload, 0, 0)
        os.chmod(seed_payload, 0o400)
        _write(self.workspace / REVIEW.blind.SEED_MANIFEST, {
            "payload_files": {"IChO2026Chem.lean": REVIEW._file_sha(seed_payload)},
        })
        self.candidate = self.workspace / f"blind_candidates/{self.record_id}.json"
        self.target = self.workspace / f"IChO2026Problems/problem_{self.record_id}.lean"
        self.blueprint = (
            self.workspace / "blueprint/src/chapters"
            / f"IChO2026Problems_problem_{self.record_id}.tex"
        )
        self.report = self.workspace / "reports/source/problem.source.json"
        workspace_image = self.workspace / "icho_2026_source/image/page.png"
        workspace_image.parent.mkdir(parents=True, exist_ok=True)
        workspace_image.write_bytes(self.image.read_bytes())
        os.chown(workspace_image, 0, 0)
        os.chmod(workspace_image, 0o400)
        blind_hash = REVIEW._sha(REVIEW._canonical(self.row))
        solver = REVIEW._load_solver_module()
        candidate = solver._construct_candidate(
            {
                "raw_result": {
                    "expression": "123/100 from printed data", "value": "1.23",
                    "lean_expression": "Fixture.rawResult",
                    "derivation_spec": "Fixture.rawDerived",
                    "certified_interval": {"lower": "1.229", "upper": "1.231"},
                    "unit": "mol",
                },
                "reported_result": {
                    "value": "1.23", "text": "1.23 mol",
                    "lean_expression": "Fixture.reportedResult", "unit": "mol",
                },
                "candidate_domain_derivation": {
                    "kind": "problem_text", "evidence": ["printed data"],
                    "depends_on": [],
                },
                "lean_declarations": ["Fixture.rawResult", "Fixture.reportedResult"],
                "lean_source": "import IChO2026Chem\n",
                "blueprint": "source-grounded proof",
            },
            target_id=self.record_id, blind_hash=blind_hash,
            source_entry=self.row,
        )
        _write(self.candidate, candidate)
        self.target.parent.mkdir(parents=True, exist_ok=True)
        self.target.write_text("import IChO2026Chem\ntheorem reviewed : True := by trivial\n")
        os.chown(self.target, 0, 0)
        os.chmod(self.target, 0o400)
        self.blueprint.parent.mkdir(parents=True, exist_ok=True)
        self.blueprint.write_text(
            "% archon:source-report reports/source/problem.source.json\n"
            "source-grounded proof\n"
        )
        os.chown(self.blueprint, 0, 0)
        os.chmod(self.blueprint, 0o400)
        _write(self.report, {
            "schema_version": 3, "evaluation_mode": "answer_blind",
            "official_answer_seen": False, "phase": "solve",
            "blind_record_sha256": blind_hash,
            "output_lean": self.target.relative_to(self.workspace).as_posix(),
            "entry": {
                **self.row, "blind_record_sha256": blind_hash,
                "image_paths": ["icho_2026_source/image/page.png"],
            },
            "previous_parts": [],
        })

    def tearDown(self) -> None:
        shutil.rmtree(self.base)

    def _source_submission(self) -> dict[str, object]:
        return {"records": [{
            "id": self.record_id, "status": "passed",
            "givens": [{
                "id": "given", "source_locator": "source.current_question",
                "fact": "the printed data define the requested quantity",
            }],
            "derivation_steps": [{
                "id": "derive", "claim": "the raw quantity is 1.23 mol",
                "depends_on": ["given"], "justification": "direct evaluation",
            }],
            "output_commitments": [{
                "id": "result", "derivation_step_ids": ["derive"],
                "result_spec": {
                    "kind": "numeric", "status": "derived",
                    "raw_expression": "123/100", "raw_value": "1.23",
                    "certified_interval": {"lower": "1.229", "upper": "1.231"},
                    "reported_value": "1.23", "reporting_quantum": "0.01",
                    "tie_rule": "half_away_from_zero",
                },
            }],
        }]}

    @staticmethod
    def _audit() -> dict[str, str]:
        return {"status": "passed", "evidence": "checked against bound source"}

    def _blind_review(self) -> dict[str, object]:
        audit = self._audit()
        return {
            "blind_source_audit": {
                name: dict(audit) for name in (
                    "answer_independence", "raw_derivation", "reporting_rule_source",
                    "tolerance_provenance", "candidate_domain_provenance",
                    "lean_result_binding",
                )
            },
            "contract_audit": {
                name: dict(audit) for name in (
                    "statement_scope", "hypothesis_derivability",
                    "conclusion_alignment", "bridge_completeness",
                )
            },
            "requested_outputs": [{
                "lean_carrier": "reviewed", "status": "passed",
                "evidence": "the carrier covers the requested quantity",
            }],
            "blueprint_conflicts": [],
            "image_audit": [{"inspected": True, "evidence": "page inspected"}],
            "chemistry_checks": {
                name: dict(audit) for name in (
                    "chemical_semantics", "staged_species_domain",
                    "formula_mass_consistency",
                    "conservation_laws", "units_dimensions", "numerical_reporting",
                    "structure_stereochemistry", "identification_uniqueness",
                    "answer_smuggling",
                )
            },
        }

    def _artifact_submission(self) -> dict[str, object]:
        audit = self._audit()
        return {"records": [{
            "id": self.record_id,
            "source_alignment": {"status": "passed", "evidence": "matches A"},
            "formalization": {
                "checks": {
                    name: dict(audit) for name in REVIEW.blind._FORMAL_REVIEW_CHECKS
                },
                "bridge_obligations": [{
                    "claim": "printed result", "carrier": "reviewed",
                    "status": "covered", "evidence": "direct theorem carrier",
                }],
                "blind_review": self._blind_review(),
            },
            "proof": {
                "proof_review_route": "solved", "reason": "proof checks",
                "evidence": "kernel-checked theorem", "redraft_kind": "not_applicable",
                "blind_review": self._blind_review(),
            },
        }]}

    def _exchange(self, variant: str):
        calls: list[tuple[str, dict[str, object]]] = []

        def exchange(
            actual_variant: str, _run: str, request: object, _directory: Path,
            target: str, _attempt: int,
        ) -> REVIEW.Exchange:
            self.assertEqual(actual_variant, variant)
            assert isinstance(request, dict)
            calls.append((target, request))
            submission = (
                self._source_submission()
                if target == "independent-source-first-review"
                else self._artifact_submission()
            )
            text = json.dumps(submission, sort_keys=True, separators=(",", ":"))
            response = (
                {"output": [{"content": [{"type": "output_text", "text": text}]}]}
                if variant == "gpt"
                else {"content": [{"type": "text", "text": text}]}
            )
            chain = ("1" if len(calls) == 1 else "2") * 64
            return REVIEW.Exchange(
                response=REVIEW._canonical(response), submission=submission,
                adapter=(
                    "chatgpt_login_proxy_v1" if variant == "gpt"
                    else "structured_broker_http_v1"
                ),
                transport={"kind": f"mock-{len(calls)}"}, chain_sha256=chain,
            )

        return calls, exchange

    def _contract(self) -> dict[str, object]:
        return {
            "valid": True, "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "target": self.target.relative_to(self.workspace).as_posix(),
            "images": [{"path": "page.png", "sha256": REVIEW._file_sha(self.image)}],
        }

    def _solver_receipt(self, *, variant: str, precommit: Path) -> Path:
        family, model = REVIEW.MODELS[variant]
        artifacts = {
            "candidate": {"path": self.candidate.relative_to(self.workspace).as_posix(), "sha256": REVIEW._file_sha(self.candidate)},
            "lean": {"path": self.target.relative_to(self.workspace).as_posix(), "sha256": REVIEW._file_sha(self.target)},
            "blueprint": {"path": self.blueprint.relative_to(self.workspace).as_posix(), "sha256": REVIEW._file_sha(self.blueprint)},
        }
        path = self.controller / f"{variant}-structured-solver-receipt.json"
        _write(path, {
            "phase": "structured_solver_aggregate", "variant": variant,
            "model_family": family, "model_id": model, "run_id": self.run_id,
            "scope_ids": [self.record_id],
            "source_first_precommit_sha256": REVIEW._file_sha(precommit),
            "all_targets_finalized": True,
            "targets": [{
                "id": self.record_id,
                "source_report": {"path": str(self.report), "sha256": REVIEW._file_sha(self.report)},
                "final_artifacts": artifacts,
            }],
        })
        return path

    def _verifier(self, snapshot: Path, snapshot_sha: str) -> Path:
        semantic = self.controller / "lean-verifier-result.json"
        _write(semantic, {
            "compiled": True, "scope_ids": [self.record_id],
            "snapshot_inventory_sha256": snapshot_sha,
        })
        wrapper = self.controller / "lean-verifier-invocation.json"
        _write(wrapper, {
            "phase": "lean_verifier_invocation", "protocol": REVIEW.PROTOCOL,
            "exit_code": 0, "solver_stopped": True, "descendants_stopped": True,
            "snapshot_inventory_sha256": snapshot_sha,
            "snapshot_root": str(snapshot),
            "verifier_receipt": {"path": str(semantic), "sha256": REVIEW._file_sha(semantic)},
        })
        return wrapper

    def _copy_snapshot(self) -> tuple[Path, dict[str, str], str]:
        root = self.base / "verifier-snapshot"
        REVIEW.blind.create_blind_verifier_snapshot(
            project=self.workspace, dependency_root=self.dependency, output=root,
        )
        files = REVIEW.blind._project_snapshot_inventory(
            self.workspace, dependency_root=self.dependency,
        )
        return root, files, REVIEW.blind._hash_index(files)

    def _run_happy(self, variant: str) -> tuple[dict[str, object], list[tuple[str, dict[str, object]]]]:
        calls, exchange = self._exchange(variant)
        precommit = REVIEW.run_source_first(
            controller_dir=self.controller, bundle_path=self.bundle,
            asset_root=self.assets, variant=variant, run_id=self.run_id,
            scope_ids=[self.record_id], exchange_call=exchange,
        )
        precommit_path = self.controller / f"{variant}-source-first-precommit.json"
        solver = self._solver_receipt(variant=variant, precommit=precommit_path)
        submission = REVIEW.run_artifact_submit(
            workspace=self.workspace, controller_dir=self.controller,
            bundle_path=self.bundle, source_first_precommit=precommit_path,
            solver_aggregate=solver, dependency_root=self.dependency,
            variant=variant, run_id=self.run_id, scope_ids=[self.record_id],
            exchange_call=exchange,
        )
        self.assertEqual(precommit["status"], "accepted")
        snapshot, files, digest = self._copy_snapshot()
        verifier = self._verifier(snapshot, digest)
        aggregate = REVIEW.run_artifact_finalize(
            workspace=self.workspace, controller_dir=self.controller,
            bundle_path=self.bundle, source_first_precommit=precommit_path,
            solver_aggregate=solver,
            artifact_submission=self.controller / f"{variant}-artifact-review-submission.json",
            verifier_invocation=verifier, verifier_snapshot=snapshot,
            dependency_root=self.dependency,
            snapshot_inventory_sha256=digest, variant=variant,
            run_id=self.run_id, scope_ids=[self.record_id],
        )
        self.assertEqual(submission["status"], "accepted")
        return aggregate, calls

    def test_mock_gpt_source_submit_finalize_and_exact_gates(self) -> None:
        aggregate, calls = self._run_happy("gpt")
        self.assertTrue(aggregate["all_passes_finalized"])
        self.assertEqual(len(calls), 2)
        self.assertNotEqual(
            aggregate["source_commitment_sha256"], aggregate["semantic_review_sha256"]
        )
        source_files = json.loads(
            (self.controller / "gpt-source-first-precommit.json").read_text()
        )["input_inventory"]["files"]
        self.assertFalse(any(path.endswith(".lean") for path in source_files))
        self.assertFalse(any("candidate" in path or "blueprint" in path for path in source_files))
        records = json.loads(
            (self.controller / "gpt-artifact-review-records.json").read_text()
        )["records"][0]
        formal = json.loads(
            (self.workspace / ".archon/formalization-review-gate.json").read_text()
        )["targets"][records["target"]]
        proof = json.loads(
            (self.workspace / ".archon/proof-review-gate.json").read_text()
        )["targets"][records["target"]]
        self.assertEqual(formal, {"status": "passed", "certificate": records["formalization_certificate"]})
        self.assertEqual(proof, {"status": "solved", **records["proof_certificate"]})

    def test_mock_kimi_has_distinct_A_to_B_transport_chain(self) -> None:
        aggregate, calls = self._run_happy("kimi-k3")
        source = json.loads(Path(aggregate["source_first_attempt"]["path"]).read_text())
        artifact = json.loads(Path(aggregate["artifact_review_attempt"]["path"]).read_text())
        self.assertEqual(len(calls), 2)
        self.assertNotEqual(
            source["request_response_chain_sha256"],
            artifact["request_response_chain_sha256"],
        )

    def test_source_first_immediately_persists_records_commitment(
        self,
    ) -> None:
        calls, exchange = self._exchange("gpt")
        precommit = REVIEW.run_source_first(
            controller_dir=self.controller, bundle_path=self.bundle,
            asset_root=self.assets, variant="gpt", run_id=self.run_id,
            scope_ids=[self.record_id], exchange_call=exchange,
        )
        path = self.controller / "gpt-source-first-records.json"
        records = json.loads(path.read_text())
        self.assertEqual(precommit["status"], "accepted")
        self.assertEqual(records["phase"], "independent_source_first_records")
        self.assertEqual(records["run_id"], self.run_id)
        self.assertEqual(records["scope_ids"], [self.record_id])
        self.assertEqual(records["records"][0]["id"], self.record_id)
        self.assertEqual(stat.S_IMODE(path.stat().st_mode), 0o400)
        self.assertEqual(len(calls), 1)
        self.assertFalse(
            (self.workspace / ".archon/source-first-records.json").exists()
        )

    def test_artifact_submit_rejects_solver_precommit_mismatch(self) -> None:
        _calls, exchange = self._exchange("gpt")
        REVIEW.run_source_first(
            controller_dir=self.controller, bundle_path=self.bundle,
            asset_root=self.assets, variant="gpt", run_id=self.run_id,
            scope_ids=[self.record_id], exchange_call=exchange,
        )
        precommit = self.controller / "gpt-source-first-precommit.json"
        solver = self._solver_receipt(variant="gpt", precommit=precommit)
        value = json.loads(solver.read_text())
        value["source_first_precommit_sha256"] = "0" * 64
        os.chmod(solver, 0o600)
        _write(solver, value)
        with self.assertRaises(REVIEW.ReviewControllerError):
            REVIEW.run_artifact_submit(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, source_first_precommit=precommit,
                solver_aggregate=solver, dependency_root=self.dependency,
                variant="gpt", run_id=self.run_id,
                scope_ids=[self.record_id], exchange_call=exchange,
            )

    def test_artifact_submit_rejects_tampered_persisted_source_records(self) -> None:
        calls, exchange = self._exchange("gpt")
        REVIEW.run_source_first(
            controller_dir=self.controller, bundle_path=self.bundle,
            asset_root=self.assets, variant="gpt", run_id=self.run_id,
            scope_ids=[self.record_id], exchange_call=exchange,
        )
        precommit = self.controller / "gpt-source-first-precommit.json"
        solver = self._solver_receipt(variant="gpt", precommit=precommit)
        records_path = self.controller / "gpt-source-first-records.json"
        self.assertTrue(records_path.is_file())
        records = json.loads(records_path.read_text(encoding="utf-8"))
        records["run_id"] = "tampered-run"
        os.chmod(records_path, 0o600)
        records_path.write_bytes(REVIEW._pretty(records))
        os.chmod(records_path, 0o400)

        with self.assertRaises(REVIEW.ReviewControllerError):
            REVIEW.run_artifact_submit(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, source_first_precommit=precommit,
                solver_aggregate=solver, dependency_root=self.dependency,
                variant="gpt", run_id=self.run_id,
                scope_ids=[self.record_id], exchange_call=exchange,
            )

        self.assertEqual(len(calls), 1)
        self.assertFalse(
            (self.controller / "gpt-artifact-review-submission.json").exists()
        )
        self.assertFalse(
            (self.workspace / ".archon/formalization-review-gate.json").exists()
        )
        self.assertFalse(
            (self.workspace / ".archon/proof-review-gate.json").exists()
        )

    def test_source_first_rejects_empty_records_without_precommit(self) -> None:
        _calls, _good_exchange = self._exchange("gpt")

        def empty_exchange(
            _variant: str, _run: str, _request: object, _directory: Path,
            _target: str, _attempt: int,
        ) -> REVIEW.Exchange:
            submission = {"records": []}
            response = {"output": [{"content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}]}
            return REVIEW.Exchange(
                response=REVIEW._canonical(response), submission=submission,
                adapter="chatgpt_login_proxy_v1",
                transport={"kind": "mock-invalid"}, chain_sha256="3" * 64,
            )

        with self.assertRaises(REVIEW.ReviewControllerError):
            REVIEW.run_source_first(
                controller_dir=self.controller, bundle_path=self.bundle,
                asset_root=self.assets, variant="gpt", run_id=self.run_id,
                scope_ids=[self.record_id], exchange_call=empty_exchange,
            )
        self.assertFalse((self.controller / "gpt-source-first-precommit.json").exists())

    def test_source_first_rejects_fabricated_source_locator(self) -> None:
        def fabricated_exchange(
            _variant: str, _run: str, _request: object, _directory: Path,
            _target: str, _attempt: int,
        ) -> REVIEW.Exchange:
            submission = self._source_submission()
            submission["records"][0]["givens"][0][
                "source_locator"
            ] = "source.fabricated_field"
            response = {"output": [{"content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}]}
            return REVIEW.Exchange(
                response=REVIEW._canonical(response), submission=submission,
                adapter="chatgpt_login_proxy_v1",
                transport={"kind": "mock-invalid-locator"},
                chain_sha256="5" * 64,
            )

        with self.assertRaises(REVIEW.ReviewControllerError):
            REVIEW.run_source_first(
                controller_dir=self.controller, bundle_path=self.bundle,
                asset_root=self.assets, variant="gpt", run_id=self.run_id,
                scope_ids=[self.record_id], exchange_call=fabricated_exchange,
            )
        self.assertFalse((self.controller / "gpt-source-first-precommit.json").exists())

    def test_source_first_accepts_underdetermined_numeric_without_rounding_fields(
        self,
    ) -> None:
        def underdetermined_exchange(
            _variant: str, _run: str, _request: object, _directory: Path,
            _target: str, _attempt: int,
        ) -> REVIEW.Exchange:
            submission = self._source_submission()
            submission["records"][0]["output_commitments"][0]["result_spec"] = {
                "kind": "numeric",
                "status": "underdetermined",
                "reason": "The source omits the time basis needed for a rate.",
                "remaining_constraints": [
                    "Supply the elapsed time or the quantity delivered per day."
                ],
            }
            response = {"output": [{"content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}]}
            return REVIEW.Exchange(
                response=REVIEW._canonical(response), submission=submission,
                adapter="chatgpt_login_proxy_v1",
                transport={"kind": "mock-underdetermined"},
                chain_sha256="6" * 64,
            )

        precommit = REVIEW.run_source_first(
            controller_dir=self.controller, bundle_path=self.bundle,
            asset_root=self.assets, variant="gpt", run_id=self.run_id,
            scope_ids=[self.record_id], exchange_call=underdetermined_exchange,
        )
        self.assertEqual(precommit["status"], "accepted")
        self.assertTrue(precommit["finalized_before_solver"])

    def test_source_first_rejects_reporting_policy_drift(self) -> None:
        def drifted_exchange(
            _variant: str, _run: str, _request: object, _directory: Path,
            _target: str, _attempt: int,
        ) -> REVIEW.Exchange:
            submission = self._source_submission()
            spec = submission["records"][0]["output_commitments"][0]["result_spec"]
            spec["reported_value"] = "1.2"
            spec["reporting_quantum"] = "0.1"
            spec["tie_rule"] = "made_up"
            response = {"output": [{"content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}]}
            return REVIEW.Exchange(
                response=REVIEW._canonical(response), submission=submission,
                adapter="chatgpt_login_proxy_v1",
                transport={"kind": "mock-policy-drift"},
                chain_sha256="7" * 64,
            )

        with self.assertRaises(REVIEW.ReviewControllerError):
            REVIEW.run_source_first(
                controller_dir=self.controller, bundle_path=self.bundle,
                asset_root=self.assets, variant="gpt", run_id=self.run_id,
                scope_ids=[self.record_id], exchange_call=drifted_exchange,
            )
        self.assertFalse((self.controller / "gpt-source-first-precommit.json").exists())

    def test_artifact_failed_audit_does_not_write_gate(self) -> None:
        calls, good_exchange = self._exchange("gpt")
        REVIEW.run_source_first(
            controller_dir=self.controller, bundle_path=self.bundle,
            asset_root=self.assets, variant="gpt", run_id=self.run_id,
            scope_ids=[self.record_id], exchange_call=good_exchange,
        )
        precommit = self.controller / "gpt-source-first-precommit.json"
        solver = self._solver_receipt(variant="gpt", precommit=precommit)

        def failed_exchange(
            variant: str, run: str, request: object, directory: Path,
            target: str, attempt: int,
        ) -> REVIEW.Exchange:
            if target != "independent-artifact-review":
                return good_exchange(variant, run, request, directory, target, attempt)
            submission = self._artifact_submission()
            submission["records"][0]["formalization"]["checks"][
                "source_faithfulness"
            ]["status"] = "failed"
            response = {"output": [{"content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}]}
            return REVIEW.Exchange(
                response=REVIEW._canonical(response), submission=submission,
                adapter="chatgpt_login_proxy_v1",
                transport={"kind": "mock-failed"}, chain_sha256="4" * 64,
            )

        contract = self._contract()
        with (
            mock.patch.object(REVIEW.blind, "build_review_source_contract", return_value=contract),
            mock.patch.object(REVIEW.blind, "is_answer_blind_contract", return_value=True),
            mock.patch.object(REVIEW.blind, "source_contract_provenance", return_value=contract),
            self.assertRaises(REVIEW.ReviewControllerError),
        ):
            REVIEW.run_artifact_submit(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, source_first_precommit=precommit,
                solver_aggregate=solver, dependency_root=self.dependency,
                variant="gpt", run_id=self.run_id,
                scope_ids=[self.record_id], exchange_call=failed_exchange,
            )
        self.assertFalse((self.workspace / ".archon/formalization-review-gate.json").exists())
        self.assertFalse((self.workspace / ".archon/proof-review-gate.json").exists())

    def test_artifact_failed_source_alignment_does_not_write_gate(self) -> None:
        _calls, good_exchange = self._exchange("gpt")
        REVIEW.run_source_first(
            controller_dir=self.controller, bundle_path=self.bundle,
            asset_root=self.assets, variant="gpt", run_id=self.run_id,
            scope_ids=[self.record_id], exchange_call=good_exchange,
        )
        precommit = self.controller / "gpt-source-first-precommit.json"
        solver = self._solver_receipt(variant="gpt", precommit=precommit)

        def failed_alignment(
            _variant: str, _run: str, _request: object, _directory: Path,
            _target: str, _attempt: int,
        ) -> REVIEW.Exchange:
            submission = self._artifact_submission()
            submission["records"][0]["source_alignment"]["status"] = "failed"
            response = {"output": [{"content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}]}
            return REVIEW.Exchange(
                response=REVIEW._canonical(response), submission=submission,
                adapter="chatgpt_login_proxy_v1",
                transport={"kind": "mock-failed-alignment"},
                chain_sha256="6" * 64,
            )

        contract = self._contract()
        with (
            mock.patch.object(REVIEW.blind, "build_review_source_contract", return_value=contract),
            mock.patch.object(REVIEW.blind, "is_answer_blind_contract", return_value=True),
            mock.patch.object(REVIEW.blind, "source_contract_provenance", return_value=contract),
            self.assertRaises(REVIEW.ReviewControllerError),
        ):
            REVIEW.run_artifact_submit(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, source_first_precommit=precommit,
                solver_aggregate=solver, dependency_root=self.dependency,
                variant="gpt", run_id=self.run_id,
                scope_ids=[self.record_id], exchange_call=failed_alignment,
            )
        self.assertFalse((self.workspace / ".archon/formalization-review-gate.json").exists())
        self.assertFalse((self.workspace / ".archon/proof-review-gate.json").exists())

    def test_cli_exposes_only_explicit_three_stage_flow(self) -> None:
        parser = REVIEW._parser()
        self.assertEqual(
            set(parser._subparsers._group_actions[0].choices),
            {"source-first", "artifact-submit", "artifact-finalize"},
        )


if __name__ == "__main__":
    unittest.main()
