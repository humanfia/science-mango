from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import os
import stat
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from archon.commands.loop.prior_result_dependency import (
    canonical_prior_result_value_sha256,
    validate_prior_result_dependency_context_self,
)


MODULE_PATH = (
    Path(__file__).resolve().parents[1]
    / "scripts/freeze_icho_a4_a5_prior_result.py"
)
SPEC = importlib.util.spec_from_file_location(
    "freeze_icho_a4_a5_prior_result_under_test", MODULE_PATH
)
assert SPEC is not None and SPEC.loader is not None
FREEZER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FREEZER)


def canonical(value: object) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


class FreezerFixture:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.producer_seed = root / "producer-seed"
        self.workspace = root / "producer-workspace"
        self.consumer_seed = root / "consumer-seed"
        for path in (self.producer_seed, self.workspace, self.consumer_seed):
            path.mkdir(mode=0o700)

        self.pdf_sha = "1" * 64
        self.producer_rows = [
            self._row(FREEZER.A4),
            self._row(FREEZER.A5),
        ]
        self.consumer_rows = [
            self._row(FREEZER.A3),
            self._row(
                FREEZER.A6,
                previous=[
                    {"source_id": FREEZER.A4, "question": "Identify Q, C, D."},
                    {"source_id": FREEZER.A5, "question": "Identify E, F, G."},
                ],
            ),
        ]
        self._write_bundle(
            self.producer_seed,
            self.producer_rows,
            FREEZER.PRODUCER_IDS,
        )
        self._write_bundle(
            self.consumer_seed,
            self.consumer_rows,
            FREEZER.CONSUMER_BUNDLE_IDS,
        )
        self._copy_producer_source_projection()

        self.formal: dict[str, object] = {"version": 1, "targets": {}}
        self.proof: dict[str, object] = {"version": 1, "targets": {}}
        self.answers: dict[str, dict[str, object]] = {}
        self.modules: dict[str, bytes] = {}
        self.axiom = {
            "ran": True,
            "error": None,
            "filesChecked": 2,
            "durationSecs": 1,
            "jobs": 2,
            "scope": "current-objectives",
            "targetFiles": [
                FREEZER._target(FREEZER.A4),
                FREEZER._target(FREEZER.A5),
            ],
            "failedFiles": [],
            "sorryLaunderings": [],
            "otherNonStandardAxioms": [],
        }
        for row in self.producer_rows:
            self._producer_artifacts(row)
        producer_bundle_sha = sha(
            (self.producer_seed / FREEZER.BUNDLE_REL).read_bytes()
        )
        self.campaign = {
            "schema_version": 1,
            "pipeline": "archon-native-answer-blind-full32",
            "workspace": str(self.workspace.resolve()),
            "row_count": 2,
            "bundle_sha256": producer_bundle_sha,
            "max_iterations": 12,
            "review_max_iterations": 6,
            "max_parallel": 2,
            "target_lifecycle": True,
            "status": "succeeded",
            "phase": "loop",
            "returncode": 0,
            "grounding": {"complete": 2},
            "native": {
                "formalization_review": {"passed": 2},
                "proof_review": {"solved": 2},
                "lake_build_ok": True,
                "sorry_count": 0,
                "complete": True,
            },
        }
        self.persist()

    def _row(
        self,
        source_id: str,
        *,
        previous: list[dict[str, str]] | None = None,
    ) -> dict[str, object]:
        requested = []
        for output_id, kind, unit in FREEZER.EXPECTED_OUTPUTS.get(source_id, ()):
            requested.append({
                "id": output_id,
                "kind": kind,
                "unit": unit,
                "source_requirement": output_id,
                "reporting_policy": {
                    "kind": "exact_symbolic",
                    "source": "problem_output_type",
                },
            })
        return {
            "schema_version": 1,
            "protocol": "icho-answer-blind-v1",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "id": source_id,
            "index": source_id,
            "problem_id": "icho_2026_t1",
            "shared_context": f"shared context through {source_id}",
            "current_question": f"question for {source_id}",
            "previous_parts": previous or [],
            "requested_outputs": requested,
            "problem_assets": [{
                "kind": "problem_pdf",
                "path": "theory_problem.pdf",
                "sha256": self.pdf_sha,
                "source_page": 1,
            }],
        }

    def _write_json(self, path: Path, value: object) -> None:
        path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        path.write_bytes(canonical(value))

    def _write_bundle(
        self,
        root: Path,
        rows: list[dict[str, object]],
        ids: tuple[str, ...],
    ) -> None:
        payload = b"".join(canonical(row) for row in rows)
        bundle = root / FREEZER.BUNDLE_REL
        bundle.parent.mkdir(mode=0o700, parents=True)
        bundle.write_bytes(payload)
        manifest = {
            "schema_version": 1,
            "protocol": "icho-problem-only-solver-seed-v1",
            "source_revision_disclosed": False,
            "target_ids": list(ids),
            "target_ids_sha256": canonical_prior_result_value_sha256(list(ids)),
            "blind_bundle_sha256": sha(payload),
            "blind_bundle": {
                "path": FREEZER.BUNDLE_REL.as_posix(),
                "row_count": len(ids),
                "sha256": sha(payload),
                "size": len(payload),
            },
        }
        self._write_json(root / FREEZER.MANIFEST_REL, manifest)

    def _copy_producer_source_projection(self) -> None:
        source_bundle = self.producer_seed / FREEZER.BUNDLE_REL
        target_bundle = self.workspace / FREEZER.BUNDLE_REL
        target_bundle.parent.mkdir(mode=0o700, parents=True)
        target_bundle.write_bytes(source_bundle.read_bytes())
        (self.workspace / FREEZER.MANIFEST_REL).write_bytes(
            (self.producer_seed / FREEZER.MANIFEST_REL).read_bytes()
        )

    def _producer_artifacts(self, row: dict[str, object]) -> None:
        source_id = str(row["id"])
        target = FREEZER._target(source_id)
        module = f"theorem result_{source_id} : True := by trivial\n".encode()
        module_sha = sha(module)
        self.modules[source_id] = module
        expected = FREEZER.EXPECTED_OUTPUTS[source_id]
        outputs = [
            {
                "id": output_id,
                "kind": kind,
                "raw_value": f"raw:{output_id}",
                "display_value": f"display:{output_id}",
                "unit": unit,
            }
            for output_id, kind, unit in expected
        ]
        answer = {
            "schema_version": 1,
            "id": source_id,
            "official_answer_seen": False,
            "outputs": outputs,
        }
        self.answers[source_id] = answer
        answer_sha = sha(canonical(answer))
        bundle_sha = sha(
            (self.producer_seed / FREEZER.BUNDLE_REL).read_bytes()
        )
        contract = {
            "schema_version": 1,
            "contract_kind": "native_problem_input_only",
            "authority": "problem-only",
            "evaluation_mode": "answer_blind",
            "target": target,
            "source_bundle": FREEZER.BUNDLE_REL.as_posix(),
            "source_bundle_sha256": bundle_sha,
            "source_record_id": source_id,
            "source_record_sha256": canonical_prior_result_value_sha256(row),
            "answer_submission": FREEZER._answer_relative(target),
            "answer_submission_sha256": answer_sha,
            "candidate": target,
            "candidate_sha256": module_sha,
        }
        rederived = []
        covered = []
        for output_id, kind, unit in expected:
            declaration = f"IChO2026Problems.{source_id}.{output_id}"
            rederived.append({
                "id": output_id,
                "kind": kind,
                "unit": unit,
                "lean_carriers": {
                    "reported_result": [declaration, f"{declaration}Proof"],
                },
            })
            covered.append({
                "output_id": output_id,
                "status": "covered",
                "submission_status": "matched",
                "reporting_policy_status": "matched",
            })
        certificate = {
            "schema_version": 1,
            "candidate_sha256": module_sha,
            "source_contract": copy.deepcopy(contract),
            "official_answer_alignment": None,
            "source_inconsistency": None,
            "independent_rederivation": {"requested_outputs": rederived},
            "requested_outputs": covered,
        }
        formal_targets = self.formal["targets"]
        assert isinstance(formal_targets, dict)
        formal_targets[target] = {
            "status": "passed",
            "candidate_sha256": module_sha,
            "certificate": certificate,
        }
        proof_targets = self.proof["targets"]
        assert isinstance(proof_targets, dict)
        proof_targets[target] = {
            "status": "solved",
            "proof_review_route": "solved",
            "candidate_sha256": module_sha,
            "last_review_iter": 1,
            "official_answer_alignment": None,
            "source_inconsistency": None,
            "source_contract": copy.deepcopy(contract),
            "blind_review_certificate": {
                "source_contract": copy.deepcopy(contract),
                "official_answer_alignment": None,
                "source_inconsistency": None,
            },
            "repair_events": [{
                "iteration": 1,
                "candidate_sha256": module_sha,
                "resulting_status": "solved",
                "preflight": {
                    "status": "passed",
                    "compiles": True,
                    "returncode": 0,
                    "sorry_count": 0,
                    "duration_bucket": "under_1m",
                },
            }],
        }

    def persist(self) -> None:
        for source_id, payload in self.modules.items():
            path = self.workspace / FREEZER._target(source_id)
            path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            path.write_bytes(payload)
        for source_id, answer in self.answers.items():
            target = FREEZER._target(source_id)
            self._write_json(
                self.workspace / FREEZER._answer_relative(target),
                answer,
            )
        self._write_json(self.workspace / FREEZER.FORMAL_GATE_REL, self.formal)
        self._write_json(self.workspace / FREEZER.PROOF_GATE_REL, self.proof)
        self._write_json(
            self.workspace / ".archon/logs/iter-001/axiom-sweep.json",
            self.axiom,
        )
        self._write_json(self.workspace.parent / "campaign.json", self.campaign)

    def checker(
        self,
        _workspace: Path,
        _target: str,
        _candidate_sha256: str,
        declarations: list[str],
    ) -> dict[str, str]:
        return {declaration: f"CheckedType ({declaration})" for declaration in declarations}

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

    def axiom_checker(
        self, _workspace: Path, target: str, candidate_sha256: str
    ) -> dict[str, object]:
        return {
            "schema_version": 1,
            "kind": "current_exact_source_axiom_audit",
            "target": target,
            "candidate_sha256": candidate_sha256,
            "status": "passed",
            "ran": True,
            "returncode": 0,
            "files_checked": 1,
            "declarations_checked": 1,
            "target_files": [target],
            "failed_files": [],
            "sorry_launderings": [],
            "nonstandard_axioms": [],
            "stdout_sha256": sha(b"axiom-ok"),
            "stderr_sha256": sha(b""),
        }

    def build(
        self, *, checker=None, compile_checker=None, axiom_checker=None,
        uid_process_checker=None,
    ) -> dict[str, object]:
        self.persist()
        return FREEZER.build_frozen_prior_result(
            producer_workspace=self.workspace,
            producer_seed=self.producer_seed,
            consumer_seed=self.consumer_seed,
            producer_inventory_sha256="a" * 64,
            consumer_inventory_sha256="b" * 64,
            declaration_type_checker=checker or self.checker,
            current_compile_checker=compile_checker or self.compile_checker,
            current_axiom_checker=axiom_checker or self.axiom_checker,
            solver_uid=0,
            uid_process_checker=(
                uid_process_checker or (lambda _uid: False)
            ),
            controller_uid=os.geteuid(),
        )


class FreezeIchoA4A5PriorResultTest(unittest.TestCase):
    def test_builds_exact_six_typed_exports_and_stages_0600(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-positive-") as raw:
            fixture = FreezerFixture(Path(raw))
            calls: list[tuple[str, list[str]]] = []

            def checker(
                _workspace: Path, target: str, candidate_sha256: str,
                declarations: list[str],
            ) -> dict[str, str]:
                calls.append((target, list(declarations)))
                return fixture.checker(
                    _workspace, target, candidate_sha256, declarations
                )

            receipt = fixture.build(checker=checker)

            self.assertEqual(
                validate_prior_result_dependency_context_self(receipt), ""
            )
            self.assertEqual(
                [producer["source_id"] for producer in receipt["producers"]],
                [FREEZER.A4, FREEZER.A5],
            )
            self.assertEqual(
                [
                    export["result_payload"]["output_id"]
                    for producer in receipt["producers"]
                    for export in producer["typed_exports"]
                ],
                [
                    "metal_q_identity",
                    "hydrated_c_formula",
                    "compound_d_formula",
                    "compound_e_structure",
                    "compound_f_structure",
                    "compound_g_structure",
                ],
            )
            self.assertEqual(len(calls), 2)
            self.assertTrue(all(len(declarations) == 3 for _, declarations in calls))
            self.assertTrue(
                receipt["producers"][0]["typed_exports"][0]["declaration"].endswith(
                    ".metal_q_identity"
                )
            )

            output = Path(raw) / "controller" / "a4-a5-for-a6.json"
            file_sha = FREEZER.write_staged_receipt(
                output, receipt, controller_uid=os.geteuid()
            )
            self.assertEqual(file_sha, sha(output.read_bytes()))
            self.assertEqual(stat.S_IMODE(output.stat().st_mode), 0o600)
            self.assertEqual(json.loads(output.read_text()), receipt)
            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError, "already exists"
            ):
                FREEZER.write_staged_receipt(
                    output, receipt, controller_uid=os.geteuid()
                )

    def _assert_rejected(self, mutation, pattern: str) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-negative-") as raw:
            fixture = FreezerFixture(Path(raw))
            mutation(fixture)
            with self.assertRaisesRegex(FREEZER.FreezePriorResultError, pattern):
                fixture.build()

    def test_rejects_every_hard_green_boundary(self) -> None:
        def formal_retry(fixture: FreezerFixture) -> None:
            target = FREEZER._target(FREEZER.A4)
            fixture.formal["targets"][target]["status"] = "retry"

        def proof_retry(fixture: FreezerFixture) -> None:
            target = FREEZER._target(FREEZER.A4)
            fixture.proof["targets"][target]["status"] = "retry"

        def candidate_drift(fixture: FreezerFixture) -> None:
            fixture.modules[FREEZER.A4] += b"-- changed after review\n"

        def source_contract_drift(fixture: FreezerFixture) -> None:
            target = FREEZER._target(FREEZER.A4)
            certificate = fixture.formal["targets"][target]["certificate"]
            certificate["source_contract"]["source_record_sha256"] = "0" * 64

        def compile_failed(fixture: FreezerFixture) -> None:
            target = FREEZER._target(FREEZER.A4)
            event = fixture.proof["targets"][target]["repair_events"][0]
            event["preflight"]["returncode"] = 1

        def sorry_present(fixture: FreezerFixture) -> None:
            target = FREEZER._target(FREEZER.A4)
            event = fixture.proof["targets"][target]["repair_events"][0]
            event["preflight"]["sorry_count"] = 1

        def axiom_empty_green(fixture: FreezerFixture) -> None:
            fixture.axiom["filesChecked"] = 0
            fixture.axiom["targetFiles"] = []

        def axiom_laundering(fixture: FreezerFixture) -> None:
            fixture.axiom["sorryLaunderings"] = [{"decl": "bad", "axiom": "sorryAx"}]

        def axiom_nonstandard(fixture: FreezerFixture) -> None:
            fixture.axiom["otherNonStandardAxioms"] = [{"decl": "bad", "axiom": "choice"}]

        def official_seen(fixture: FreezerFixture) -> None:
            fixture.answers[FREEZER.A4]["official_answer_seen"] = True
            target = FREEZER._target(FREEZER.A4)
            answer_sha = sha(canonical(fixture.answers[FREEZER.A4]))
            for contract in (
                fixture.formal["targets"][target]["certificate"]["source_contract"],
                fixture.proof["targets"][target]["source_contract"],
                fixture.proof["targets"][target]["blind_review_certificate"][
                    "source_contract"
                ],
            ):
                contract["answer_submission_sha256"] = answer_sha

        def missing_output(fixture: FreezerFixture) -> None:
            fixture.answers[FREEZER.A4]["outputs"].pop()
            target = FREEZER._target(FREEZER.A4)
            answer_sha = sha(canonical(fixture.answers[FREEZER.A4]))
            for contract in (
                fixture.formal["targets"][target]["certificate"]["source_contract"],
                fixture.proof["targets"][target]["source_contract"],
                fixture.proof["targets"][target]["blind_review_certificate"][
                    "source_contract"
                ],
            ):
                contract["answer_submission_sha256"] = answer_sha

        def no_reported_result(fixture: FreezerFixture) -> None:
            target = FREEZER._target(FREEZER.A4)
            entries = fixture.formal["targets"][target]["certificate"][
                "independent_rederivation"
            ]["requested_outputs"]
            entries[0]["lean_carriers"]["reported_result"] = []

        cases = (
            ("formal", formal_retry, "hard-green/bound"),
            ("proof", proof_retry, "hard-green/bound"),
            ("candidate", candidate_drift, "hard-green/bound"),
            ("source contract", source_contract_drift, "source contract is stale"),
            ("compile", compile_failed, "compile/sorry"),
            ("sorry", sorry_present, "compile/sorry"),
            ("empty axiom green", axiom_empty_green, "did not cleanly cover"),
            ("sorry laundering", axiom_laundering, "did not cleanly cover"),
            ("nonstandard axiom", axiom_nonstandard, "did not cleanly cover"),
            ("official answer", official_seen, "not blind/exact"),
            ("missing answer output", missing_output, "output count"),
            ("missing carrier", no_reported_result, "invalid reported_result"),
        )
        for label, mutation, pattern in cases:
            with self.subTest(label=label):
                self._assert_rejected(mutation, pattern)

    def test_accepts_formal_old_candidate_then_proof_repaired_final(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-formal-old-") as raw:
            fixture = FreezerFixture(Path(raw))
            target = FREEZER._target(FREEZER.A4)
            old_sha256 = "f" * 64
            formal = fixture.formal["targets"][target]
            formal["candidate_sha256"] = old_sha256
            certificate = formal["certificate"]
            certificate["candidate_sha256"] = old_sha256
            certificate["source_contract"]["candidate_sha256"] = old_sha256
            receipt = fixture.build()
            producer = receipt["producers"][0]
            self.assertEqual(
                producer["formalization_review"]["candidate_sha256"], old_sha256
            )
            self.assertEqual(
                producer["proof_review"]["candidate_sha256"],
                producer["module_sha256"],
            )

    def test_rejects_stale_formal_candidate_lineage(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-formal-stale-") as raw:
            fixture = FreezerFixture(Path(raw))
            target = FREEZER._target(FREEZER.A4)
            fixture.formal["targets"][target]["certificate"][
                "candidate_sha256"
            ] = "f" * 64
            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError,
                "formal certificate candidate hash is stale",
            ):
                fixture.build()

    def test_rejects_nonterminal_campaign_and_active_solver(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-campaign-stale-") as raw:
            fixture = FreezerFixture(Path(raw))
            fixture.campaign["status"] = "incomplete"
            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError, "not terminal hard-green"
            ):
                fixture.build()
        with tempfile.TemporaryDirectory(prefix="freezer-active-solver-") as raw:
            fixture = FreezerFixture(Path(raw))
            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError, "still has a process before freeze"
            ):
                fixture.build(uid_process_checker=lambda _uid: True)

    def test_rejects_stale_current_compile_and_axiom_audits(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-current-compile-") as raw:
            fixture = FreezerFixture(Path(raw))

            def stale_compile(workspace, target, candidate_sha256):
                result = fixture.compile_checker(workspace, target, candidate_sha256)
                result["candidate_sha256"] = "0" * 64
                return result

            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError,
                "current compile/sorry audit is not hard-green",
            ):
                fixture.build(compile_checker=stale_compile)
        with tempfile.TemporaryDirectory(prefix="freezer-current-axiom-") as raw:
            fixture = FreezerFixture(Path(raw))

            def laundering_axiom(workspace, target, candidate_sha256):
                result = fixture.axiom_checker(workspace, target, candidate_sha256)
                result["status"] = "failed"
                result["sorry_launderings"] = [{
                    "decl": "Bad", "axiom": "sorryAx"
                }]
                result["failed_files"] = [target]
                return result

            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError,
                "current axiom audit is not hard-green/exact",
            ):
                fixture.build(axiom_checker=laundering_axiom)

    def test_rejects_module_toctou_during_exact_type_check(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-module-toctou-") as raw:
            fixture = FreezerFixture(Path(raw))

            def changing_checker(
                workspace: Path, target: str, candidate_sha256: str,
                declarations: list[str],
            ) -> dict[str, str]:
                result = fixture.checker(
                    workspace, target, candidate_sha256, declarations
                )
                with (workspace / target).open("ab") as stream:
                    stream.write(b"-- changed during check\n")
                return result

            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError,
                "Lean module changed during current audits",
            ):
                fixture.build(checker=changing_checker)

    def test_rejects_incomplete_lean_type_check(self) -> None:
        with tempfile.TemporaryDirectory(prefix="freezer-type-negative-") as raw:
            fixture = FreezerFixture(Path(raw))

            def incomplete(
                _workspace: Path, _target: str, _candidate_sha256: str,
                declarations: list[str],
            ) -> dict[str, str]:
                return {declarations[0]: "Nat"}

            with self.assertRaisesRegex(
                FREEZER.FreezePriorResultError, "incomplete declaration map"
            ):
                fixture.build(checker=incomplete)

    def test_production_type_checker_runs_lake_and_parses_exact_types(self) -> None:
        declarations = ["Example.first", "Example.second"]
        payload = (
            b"namespace Example\n"
            b"def first : Nat := 1\n"
            b"def second : List Nat := []\n"
            b"end Example\n"
        )
        completed = SimpleNamespace(
            returncode=0,
            stdout="Example.first : Nat\nExample.second : List Nat\n",
            stderr="",
        )
        seen_source: list[bytes] = []
        with tempfile.TemporaryDirectory(prefix="freezer-lean-runner-") as raw:
            workspace = Path(raw)
            target = "IChO2026Problems/problem_icho_2026_t1_a4.lean"
            target_path = workspace / target
            target_path.parent.mkdir(parents=True)
            target_path.write_bytes(payload)

            def fake_run(command, **_kwargs):
                seen_source.append(Path(command[-1]).read_bytes())
                return completed

            with mock.patch.object(FREEZER.subprocess, "run", side_effect=fake_run) as run:
                result = FREEZER.lean_declaration_types(
                    workspace, target, sha(payload), declarations,
                    lake_bin=Path("/controller/bin/lake"), timeout_seconds=17,
                )
        self.assertEqual(result, {
            "Example.first": "Nat",
            "Example.second": "List Nat",
        })
        command = run.call_args.args[0]
        self.assertEqual(command[:3], ["/controller/bin/lake", "env", "lean"])
        self.assertEqual(run.call_args.kwargs["cwd"], workspace)
        self.assertEqual(run.call_args.kwargs["timeout"], 17)
        self.assertEqual(len(seen_source), 1)
        self.assertTrue(seen_source[0].startswith(payload))
        self.assertIn(b"#check Example.first", seen_source[0])
        self.assertIn(
            b"set_option format.width 1000000 in", seen_source[0]
        )
        self.assertNotIn(b"set_option pp.width", seen_source[0])
        self.assertNotIn(b"import IChO2026Problems", seen_source[0])

    def test_production_type_checker_parses_strict_multiline_type_block(self) -> None:
        declarations = ["Example.first", "Example.second"]
        payload = b"namespace Example\ndef first := 1\ndef second := 2\nend Example\n"
        completed = SimpleNamespace(
            returncode=0,
            stdout=(
                "Example.first : Nat\n"
                "Example.second :\n"
                "  Very.Long.Type\n"
                "    (List   Nat)\n"
            ),
            stderr="",
        )
        with tempfile.TemporaryDirectory(prefix="freezer-lean-multiline-") as raw:
            workspace = Path(raw)
            target = "IChO2026Problems/problem_icho_2026_t1_a4.lean"
            target_path = workspace / target
            target_path.parent.mkdir(parents=True)
            target_path.write_bytes(payload)
            with mock.patch.object(FREEZER.subprocess, "run", return_value=completed):
                result = FREEZER.lean_declaration_types(
                    workspace, target, sha(payload), declarations,
                    lake_bin=Path("/controller/bin/lake"), timeout_seconds=17,
                )
        self.assertEqual(result, {
            "Example.first": "Nat",
            "Example.second": "Very.Long.Type (List Nat)",
        })

    def test_production_type_checker_parses_inline_then_continuation(self) -> None:
        declarations = ["Example.first", "Example.second"]
        payload = b"def fixture := 1\n"
        completed = SimpleNamespace(
            returncode=0,
            stdout=(
                "Example.first : FirstPart\n"
                "  ContinuedPart\n"
                "Example.second : Nat\n"
            ),
            stderr="",
        )
        with tempfile.TemporaryDirectory(
            prefix="freezer-lean-inline-continuation-"
        ) as raw:
            workspace = Path(raw)
            target = "IChO2026Problems/problem_icho_2026_t1_a4.lean"
            target_path = workspace / target
            target_path.parent.mkdir(parents=True)
            target_path.write_bytes(payload)
            with mock.patch.object(FREEZER.subprocess, "run", return_value=completed):
                result = FREEZER.lean_declaration_types(
                    workspace, target, sha(payload), declarations,
                    lake_bin=Path("/controller/bin/lake"), timeout_seconds=17,
                )
        self.assertEqual(result, {
            "Example.first": "FirstPart ContinuedPart",
            "Example.second": "Nat",
        })

    def test_production_type_checker_rejects_non_block_output(self) -> None:
        declarations = ["Example.first", "Example.second"]
        payload = b"def fixture := 1\n"
        invalid_outputs = {
            "warning": "warning: drift\nExample.first : Nat\nExample.second : Nat\n",
            "extra": "Example.first : Nat\nextra output\nExample.second : Nat\n",
            "duplicate": "Example.first : Nat\nExample.first : Nat\nExample.second : Nat\n",
            "missing": "Example.first : Nat\n",
            "out_of_order": "Example.second : Nat\nExample.first : Nat\n",
            "empty": "Example.first :\nExample.second : Nat\n",
        }
        for label, stdout in invalid_outputs.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory(
                prefix="freezer-lean-invalid-"
            ) as raw:
                workspace = Path(raw)
                target = "IChO2026Problems/problem_icho_2026_t1_a4.lean"
                target_path = workspace / target
                target_path.parent.mkdir(parents=True)
                target_path.write_bytes(payload)
                completed = SimpleNamespace(returncode=0, stdout=stdout, stderr="")
                with mock.patch.object(
                    FREEZER.subprocess, "run", return_value=completed
                ), self.assertRaises(FREEZER.FreezePriorResultError):
                    FREEZER.lean_declaration_types(
                        workspace, target, sha(payload), declarations,
                        lake_bin=Path("/controller/bin/lake"), timeout_seconds=17,
                    )


if __name__ == "__main__":
    unittest.main()
