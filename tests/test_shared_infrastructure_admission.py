from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from typer.testing import CliRunner

import archon.commands.loop.shared_infrastructure_admission as admission_module
from archon.commands.loop.shared_infrastructure import (
    EXTERNAL_KIND,
    PROJECT_LOCAL_KIND,
    load_shared_infrastructure_state,
    pending_shared_infrastructure_objectives,
)
from archon.commands.loop.shared_infrastructure_admission import (
    SharedInfrastructureAdmissionError,
    admit_explicit_user_architecture_request,
)
from archon.cli import app as archon_app


MODULE = "IChO2026Chem/Kinetics/BelousovZhabotinsky.lean"
NAMESPACE = "IChO2026Chem.Kinetics.BelousovZhabotinsky"
A2 = "IChO2026Problems/problem_icho_2026_t2_a2.lean"
A3 = "IChO2026Problems/problem_icho_2026_t2_a3.lean"
A5 = "IChO2026Problems/problem_icho_2026_t2_a5.lean"


class SharedInfrastructureAdmissionTest(unittest.TestCase):
    def _project(self, root: Path) -> Path:
        state = root / ".archon"
        state.mkdir()
        (state / "config.json").write_text(json.dumps({
            "loop": {
                "proof_review_max_iterations": 3,
                "shared_infrastructure": {
                    "enabled": True,
                    "module_roots": ["IChO2026Chem"],
                    "scaffolder": "chemistry-module-refactor",
                    "migration_refactor": "refactor",
                },
            },
        }), encoding="utf-8")
        for rel in (A2, A3, A5):
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                f"theorem {path.stem} : True := by trivial\n",
                encoding="utf-8",
            )
        return state

    @staticmethod
    def _request(*declarations: str) -> dict:
        return {
            "kind": PROJECT_LOCAL_KIND,
            "module": MODULE,
            "declarations": list(declarations),
        }

    @staticmethod
    def _seed_solved_gate(state: Path) -> None:
        (state / "proof-review-gate.json").write_text(
            json.dumps({
                "version": 2,
                "max_iterations": 3,
                "targets": {
                    A2: {
                        "status": "solved",
                        "attempts": 1,
                        "reason": "proof review passed",
                        "history": [{"iter": 6, "route": "solved"}],
                    },
                    A3: {
                        "status": "solved",
                        "attempts": 2,
                        "reason": "proof review passed",
                        "history": [{"iter": 6, "route": "solved"}],
                    },
                },
            }, indent=2) + "\n",
            encoding="utf-8",
        )

    @staticmethod
    def _add_module_gate_record(
        state: Path, status: str = "solved",
    ) -> None:
        gate_path = state / "proof-review-gate.json"
        gate = json.loads(gate_path.read_text(encoding="utf-8"))
        gate["targets"][MODULE] = {
            "status": status,
            "attempts": 1,
            "reason": f"old shared-module proof review is {status}",
            "evidence": "ordinary review record for the previous shared API",
            "history": [{"iter": 6, "route": status}],
        }
        gate_path.write_text(
            json.dumps(gate, indent=2) + "\n",
            encoding="utf-8",
        )

    @staticmethod
    def _seed_verified_shared_module(
        root: Path, state: Path, *declarations: str,
    ) -> Path:
        module = root / MODULE
        module.parent.mkdir(parents=True, exist_ok=True)
        module.write_text(
            "namespace IChO2026Chem.Kinetics.BelousovZhabotinsky\n"
            "def Species := Nat\n"
            "end IChO2026Chem.Kinetics.BelousovZhabotinsky\n",
            encoding="utf-8",
        )
        (state / "shared-infrastructure.json").write_text(
            json.dumps({
                "version": 1,
                "modules": {
                    MODULE: {
                        "status": "resolved",
                        "module": MODULE,
                        "declarations": list(declarations),
                        "dependents": [A2],
                        "consumer_migrations": {
                            A2: {"status": "resolved"},
                        },
                        "verified_sha256": hashlib.sha256(
                            module.read_bytes()
                        ).hexdigest(),
                    },
                },
            }, indent=2) + "\n",
            encoding="utf-8",
        )
        return module

    def test_three_consumers_are_admitted_and_solved_targets_are_audited(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_solved_gate(state)

            result = admit_explicit_user_architecture_request(
                state_dir=state,
                project_path=root,
                raw_request=self._request(
                    f"{NAMESPACE}.Species",
                    f"{NAMESPACE}.KineticParameters",
                    f"{NAMESPACE}.rate1",
                ),
                consumers=[A2, A3, A5],
                reason="T2 kinetics must use one shared BZ model",
                evidence="A2/A3 duplicate rate carriers; A5 is a third consumer",
                iter_num=7,
            )

            self.assertEqual(result.consumers, (A2, A3, A5))
            self.assertEqual(result.transitioned_from_solved, (A2, A3))
            queued = pending_shared_infrastructure_objectives(
                state_dir=state, project_path=root,
            )
            self.assertEqual(len(queued), 1)
            self.assertEqual(queued[0].module_path, MODULE)
            self.assertEqual(queued[0].dependents, (A2, A3, A5))

            gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            for rel in (A2, A3, A5):
                record = gate["targets"][rel]
                self.assertEqual(record["status"], "blocked_infrastructure")
                self.assertEqual(record["infrastructure_request"], result.request)
                self.assertEqual(
                    record["history"][-1]["event"],
                    "explicit_user_architecture_request_admitted",
                )
                self.assertEqual(record["history"][-1]["module"], MODULE)
                self.assertEqual(record["architecture_request_iter"], 7)
            self.assertEqual(gate["targets"][A2]["attempts"], 1)
            self.assertEqual(gate["targets"][A3]["attempts"], 2)
            self.assertEqual(gate["targets"][A5]["attempts"], 0)
            self.assertEqual(
                gate["targets"][A2]["history"][-1]["prior_status"],
                "solved",
            )
            self.assertEqual(
                gate["targets"][A5]["history"][-1]["prior_status"],
                "unreviewed",
            )

    def test_separate_admissions_coalesce_module_consumers_and_declarations(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_solved_gate(state)

            admit_explicit_user_architecture_request(
                state_dir=state,
                project_path=root,
                raw_request=self._request(f"{NAMESPACE}.Species"),
                consumers=[A2, A3],
                reason="share the BZ species carrier",
                iter_num=7,
            )
            admit_explicit_user_architecture_request(
                state_dir=state,
                project_path=root,
                raw_request=self._request(
                    f"{NAMESPACE}.KineticParameters",
                    f"{NAMESPACE}.rate4",
                ),
                consumers=[A5],
                reason="A5 reuses the BZ kinetic parameters and rate law",
                iter_num=7,
            )

            queue = load_shared_infrastructure_state(state)
            self.assertEqual(list(queue["modules"]), [MODULE])
            record = queue["modules"][MODULE]
            self.assertEqual(record["dependents"], [A2, A3, A5])
            self.assertEqual(record["declarations"], [
                f"{NAMESPACE}.KineticParameters",
                f"{NAMESPACE}.Species",
                f"{NAMESPACE}.rate4",
            ])

    def test_new_or_enlarged_contract_drops_stale_module_proof_certificate(self):
        scenarios = ("new", "enlarged")
        certificate_statuses = ("solved", "passed")
        for scenario in scenarios:
            for certificate_status in certificate_statuses:
                with (
                    self.subTest(
                        scenario=scenario,
                        certificate_status=certificate_status,
                    ),
                    tempfile.TemporaryDirectory() as td,
                ):
                    root = Path(td)
                    state = self._project(root)
                    self._seed_solved_gate(state)
                    self._add_module_gate_record(state, certificate_status)
                    if scenario == "enlarged":
                        self._seed_verified_shared_module(
                            root, state, f"{NAMESPACE}.Species",
                        )

                    admit_explicit_user_architecture_request(
                        state_dir=state,
                        project_path=root,
                        raw_request=self._request(f"{NAMESPACE}.rate6"),
                        consumers=[A2],
                        reason="extend the shared BZ API",
                        iter_num=7,
                    )

                    shared = load_shared_infrastructure_state(state)
                    self.assertIsNone(
                        shared["modules"][MODULE].get("verified_sha256")
                    )
                    gate = json.loads(
                        (state / "proof-review-gate.json").read_text(
                            encoding="utf-8"
                        )
                    )
                    self.assertNotIn(MODULE, gate["targets"])
                    self.assertEqual(
                        gate["targets"][A2]["status"],
                        "blocked_infrastructure",
                    )

    def test_non_success_module_review_records_are_preserved_for_audit(self):
        for status in ("retry", "needs_redraft", "proof_review_exhausted"):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                state = self._project(root)
                self._seed_solved_gate(state)
                self._add_module_gate_record(state, status)
                before = json.loads(
                    (state / "proof-review-gate.json").read_text(
                        encoding="utf-8"
                    )
                )["targets"][MODULE]

                admit_explicit_user_architecture_request(
                    state_dir=state,
                    project_path=root,
                    raw_request=self._request(f"{NAMESPACE}.Species"),
                    consumers=[A2],
                    reason="queue a new shared BZ API",
                    iter_num=7,
                )

                gate = json.loads(
                    (state / "proof-review-gate.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertEqual(gate["targets"][MODULE], before)

    def test_reusable_shared_verification_keeps_module_proof_certificate(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_solved_gate(state)
            self._add_module_gate_record(state)
            declaration = f"{NAMESPACE}.Species"
            module = self._seed_verified_shared_module(
                root, state, declaration,
            )
            expected_sha256 = hashlib.sha256(module.read_bytes()).hexdigest()

            admit_explicit_user_architecture_request(
                state_dir=state,
                project_path=root,
                raw_request=self._request(declaration),
                consumers=[A3],
                reason="reuse the verified shared BZ API",
                iter_num=7,
            )

            shared = load_shared_infrastructure_state(state)
            self.assertEqual(
                shared["modules"][MODULE]["verified_sha256"],
                expected_sha256,
            )
            gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertEqual(gate["targets"][MODULE]["status"], "solved")
            self.assertEqual(
                gate["targets"][A3]["status"],
                "blocked_infrastructure",
            )

    def test_missing_or_changed_module_invalidates_reusable_verification(self):
        for mutation in ("missing", "changed"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                state = self._project(root)
                self._seed_solved_gate(state)
                self._add_module_gate_record(state)
                declaration = f"{NAMESPACE}.Species"
                module = self._seed_verified_shared_module(
                    root, state, declaration,
                )
                if mutation == "missing":
                    module.unlink()
                else:
                    module.write_text(
                        "def changedSharedApi := True\n",
                        encoding="utf-8",
                    )

                admit_explicit_user_architecture_request(
                    state_dir=state,
                    project_path=root,
                    raw_request=self._request(declaration),
                    consumers=[A3],
                    reason="reuse only current shared verification",
                    iter_num=7,
                )

                shared = load_shared_infrastructure_state(state)
                record = shared["modules"][MODULE]
                self.assertEqual(record["status"], "pending")
                self.assertIsNone(record.get("verified_sha256"))
                gate = json.loads(
                    (state / "proof-review-gate.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertNotIn(MODULE, gate["targets"])

    def test_gate_publish_failure_leaves_queue_untouched_and_is_retryable(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_solved_gate(state)
            self._add_module_gate_record(state)
            gate_path = state / "proof-review-gate.json"
            gate_before = gate_path.read_bytes()
            calls: list[str] = []

            def fail_gate(path: Path, data: dict) -> None:
                del data
                calls.append(path.name)
                raise OSError("injected proof-gate write failure")

            with patch.object(
                admission_module, "_write_json_atomic", side_effect=fail_gate,
            ):
                with self.assertRaisesRegex(
                    SharedInfrastructureAdmissionError,
                    "shared queue was not published",
                ):
                    admit_explicit_user_architecture_request(
                        state_dir=state,
                        project_path=root,
                        raw_request=self._request(f"{NAMESPACE}.Species"),
                        consumers=[A2],
                        reason="exercise gate-first publication",
                        iter_num=7,
                    )

            self.assertEqual(calls, ["proof-review-gate.json"])
            self.assertEqual(gate_path.read_bytes(), gate_before)
            self.assertFalse((state / "shared-infrastructure.json").exists())

            admit_explicit_user_architecture_request(
                state_dir=state,
                project_path=root,
                raw_request=self._request(f"{NAMESPACE}.Species"),
                consumers=[A2],
                reason="exercise gate-first publication",
                iter_num=7,
            )
            self.assertTrue((state / "shared-infrastructure.json").is_file())

    def test_queue_publish_failure_is_fail_closed_and_retryable(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_solved_gate(state)
            self._add_module_gate_record(state)
            calls: list[str] = []
            real_write = admission_module._write_json_atomic

            def fail_queue(path: Path, data: dict) -> None:
                calls.append(path.name)
                if path.name == "shared-infrastructure.json":
                    raise OSError("injected shared-queue write failure")
                real_write(path, data)

            with patch.object(
                admission_module, "_write_json_atomic", side_effect=fail_queue,
            ):
                with self.assertRaisesRegex(
                    SharedInfrastructureAdmissionError,
                    "proof gate was published fail-closed",
                ):
                    admit_explicit_user_architecture_request(
                        state_dir=state,
                        project_path=root,
                        raw_request=self._request(f"{NAMESPACE}.Species"),
                        consumers=[A2],
                        reason="exercise recoverable queue failure",
                        iter_num=7,
                    )

            self.assertEqual(calls, [
                "proof-review-gate.json",
                "shared-infrastructure.json",
            ])
            self.assertFalse((state / "shared-infrastructure.json").exists())
            gate = json.loads(
                (state / "proof-review-gate.json").read_text(encoding="utf-8")
            )
            self.assertNotIn(MODULE, gate["targets"])
            self.assertEqual(
                gate["targets"][A2]["status"], "blocked_infrastructure",
            )

            admit_explicit_user_architecture_request(
                state_dir=state,
                project_path=root,
                raw_request=self._request(f"{NAMESPACE}.Species"),
                consumers=[A2],
                reason="exercise recoverable queue failure",
                iter_num=7,
            )
            self.assertTrue((state / "shared-infrastructure.json").is_file())

    def test_missing_or_unsafe_consumer_rejects_whole_batch_without_writes(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_solved_gate(state)
            gate_path = state / "proof-review-gate.json"
            gate_before = gate_path.read_bytes()

            for consumers in (
                [A2, "IChO2026Problems/missing.lean"],
                [A2, "../outside.lean"],
                [A2, MODULE],
            ):
                with self.subTest(consumers=consumers):
                    with self.assertRaises(SharedInfrastructureAdmissionError):
                        admit_explicit_user_architecture_request(
                            state_dir=state,
                            project_path=root,
                            raw_request=self._request(f"{NAMESPACE}.Species"),
                            consumers=consumers,
                            reason="invalid batch must not partially register",
                            iter_num=7,
                        )
                    self.assertEqual(gate_path.read_bytes(), gate_before)
                    self.assertFalse(
                        (state / "shared-infrastructure.json").exists()
                    )

    def test_external_dependency_and_conflicting_gate_state_are_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)

            with self.assertRaisesRegex(
                SharedInfrastructureAdmissionError,
                "external dependencies are never installed",
            ):
                admit_explicit_user_architecture_request(
                    state_dir=state,
                    project_path=root,
                    raw_request={
                        "kind": EXTERNAL_KIND,
                        "package": "untrusted-package",
                    },
                    consumers=[A2],
                    reason="external package",
                    iter_num=1,
                )
            self.assertFalse((state / "shared-infrastructure.json").exists())

            (state / "proof-review-gate.json").write_text(json.dumps({
                "version": 2,
                "targets": {A2: {
                    "status": "needs_redraft",
                    "history": [],
                }},
            }), encoding="utf-8")
            with self.assertRaisesRegex(
                SharedInfrastructureAdmissionError,
                "conflicting proof-gate status",
            ):
                admit_explicit_user_architecture_request(
                    state_dir=state,
                    project_path=root,
                    raw_request=self._request(f"{NAMESPACE}.Species"),
                    consumers=[A2],
                    reason="must not hide modeling redraft",
                    iter_num=1,
                )
            self.assertFalse((state / "shared-infrastructure.json").exists())

    def test_cli_queues_only_project_local_requests(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = self._project(root)
            self._seed_solved_gate(state)
            runner = CliRunner()

            result = runner.invoke(archon_app, [
                "shared-infrastructure",
                "request",
                str(root),
                "--module", MODULE,
                "--declaration", f"{NAMESPACE}.Species",
                "--consumer", A2,
                "--reason", "share one BZ species model",
                "--iteration", "7",
            ])

            self.assertEqual(result.exit_code, 0, result.output)
            queued = pending_shared_infrastructure_objectives(
                state_dir=state, project_path=root,
            )
            self.assertEqual([item.module_path for item in queued], [MODULE])
            self.assertFalse((root / "lake-manifest.json").exists())


if __name__ == "__main__":
    unittest.main()
