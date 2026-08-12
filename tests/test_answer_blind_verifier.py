from __future__ import annotations

import importlib.util
import os
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_answer_blind_verifier.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_verifier", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
verifier = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verifier)


class AnswerBlindVerifierControllerTest(unittest.TestCase):
    def _fixture(self, root: Path, *, exit_code: int = 0) -> dict[str, Path]:
        root.chmod(0o755)
        snapshot = root / "snapshot"
        dependency = root / "dependencies"
        runtime = root / "runtime"
        controller = root / "controller"
        scratch = root / "scratch"
        for directory in (snapshot, dependency, runtime, scratch):
            directory.mkdir(mode=0o755)
        controller.mkdir(mode=0o700)
        (snapshot / "sealed.txt").write_bytes(b"sealed snapshot\n")
        (dependency / "Mathlib.olean").write_bytes(b"sealed dependency\n")
        lake = runtime / "lake"
        lake.write_bytes(b"trusted lake\n")
        lake.chmod(0o755)
        archon = runtime / "archon"
        archon.write_text(
            textwrap.dedent(
                f"""\
                #!/usr/bin/python3
                import argparse, hashlib, json, os
                p = argparse.ArgumentParser()
                p.add_argument('command')
                p.add_argument('--project')
                p.add_argument('--candidate-dir')
                p.add_argument('--output')
                p.add_argument('--runtime-executable')
                p.add_argument('--runtime-root')
                p.add_argument('--dependency-root')
                p.add_argument('--expected-dependency-inventory-sha256')
                p.add_argument('--expected-runtime-inventory-sha256')
                p.add_argument('--expected-snapshot-inventory-sha256')
                p.add_argument('--timeout-s')
                p.add_argument('--scope-id', action='append')
                a = p.parse_args()
                if {exit_code}:
                    raise SystemExit({exit_code})
                h = lambda b: hashlib.sha256(b).hexdigest()
                runtime_bytes = open(a.runtime_executable, 'rb').read()
                records = []
                for record_id in sorted(a.scope_id):
                    records.append({{
                        'id': record_id,
                        'target': 'Problems/T1A1.lean', 'target_sha256': '1' * 64,
                        'candidate': 'blind_candidates/' + record_id + '.json',
                        'candidate_sha256': '2' * 64,
                        'source_contract_sha256': '3' * 64,
                        'result_contracts_sha256': '4' * 64,
                        'checks': [
                            {{'role': role, 'declaration': 'Fixture.' + role,
                              'normalized_type_sha256': '5' * 64,
                              'result_payload_sha256': '6' * 64,
                              'axioms': [], 'compiled': True}}
                            for role in ('raw_result', 'reported_result')
                        ],
                    }})
                value = {{
                    'schema_version': 1, 'protocol': 'icho-answer-blind-v1',
                    'phase': 'lean_verify', 'evaluation_mode': 'answer_blind',
                    'verifier_uid': os.geteuid(), 'network_answer_blind': False,
                    'runtime_executable': {{'path': a.runtime_executable,
                                             'sha256': h(runtime_bytes)}},
                    'dependency_inventory_sha256': a.expected_dependency_inventory_sha256,
                    'runtime_inventory_sha256': a.expected_runtime_inventory_sha256,
                    'snapshot_inventory_sha256': a.expected_snapshot_inventory_sha256,
                    'scope_ids': sorted(a.scope_id), 'records': records,
                    'compiled': True, 'stdout_sha256': h(b'out'),
                    'stderr_sha256': h(b''),
                }}
                payload = (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\\n').encode()
                fd = os.open(a.output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
                os.write(fd, payload); os.close(fd)
                """
            ),
            encoding="utf-8",
        )
        archon.chmod(0o755)
        for directory in (snapshot, dependency, runtime):
            for path in directory.rglob("*"):
                if path.is_file() and path != archon and path != lake:
                    path.chmod(0o444)
            directory.chmod(0o755)
        return {
            "snapshot": snapshot, "dependency": dependency,
            "runtime": runtime, "controller": controller, "scratch": scratch,
            "archon": archon, "lake": lake,
        }

    @unittest.skipUnless(os.geteuid() == 0, "controller test requires root")
    def test_root_runner_emits_exact_quiescent_wrapper(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self._fixture(Path(td))
            output = paths["controller"] / "verifier-invocation.json"
            wrapper = verifier.run_verifier(
                snapshot_root=paths["snapshot"],
                controller_dir=paths["controller"],
                runtime_root=paths["runtime"],
                dependency_root=paths["dependency"],
                archon_executable=paths["archon"],
                lake_executable=paths["lake"],
                verifier_user="ichoblindgptv", scratch_root=paths["scratch"],
                output=output, scope_ids=["icho_t1_a1"], timeout_s=10,
            )
            self.assertEqual(set(wrapper), verifier.blind._VERIFIER_INVOCATION_FIELDS)
            self.assertEqual(wrapper["snapshot_root"], str(paths["snapshot"]))
            self.assertTrue(wrapper["dedicated_uid_quiescence"]["quiescent_after"])
            self.assertEqual(output.stat().st_mode & 0o777, 0o400)
            self.assertEqual(
                Path(wrapper["verifier_receipt"]["path"]).stat().st_mode & 0o777,
                0o400,
            )

    @unittest.skipUnless(os.geteuid() == 0, "controller test requires root")
    def test_root_runner_rejects_nonzero_or_nonquiescent_verifier(self):
        with self.subTest("nonzero"), tempfile.TemporaryDirectory() as td:
            paths = self._fixture(Path(td), exit_code=9)
            with self.assertRaisesRegex(
                verifier.VerifierControllerError, "exited unsuccessfully"
            ):
                verifier.run_verifier(
                    snapshot_root=paths["snapshot"],
                    controller_dir=paths["controller"],
                    runtime_root=paths["runtime"],
                    dependency_root=paths["dependency"],
                    archon_executable=paths["archon"],
                    lake_executable=paths["lake"],
                    verifier_user="ichoblindgptv", scratch_root=paths["scratch"],
                    output=paths["controller"] / "failed.json",
                    scope_ids=["icho_t1_a1"], timeout_s=10,
                )
        with self.subTest("residual pid"), tempfile.TemporaryDirectory() as td:
            paths = self._fixture(Path(td))
            bad = {
                "mechanism": "dedicated_uid_prlimit_pidfd_v1", "uid": 995,
                "rlimit_nproc": 64, "quiescent_before": True, "before_pids": [],
                "prlimit_zero_applied": True, "pidfd_kill_used": True,
                "kill_rounds": 1, "quiet_period_ms": 500,
                "after_pids": [12345], "quiescent_after": False,
            }
            with mock.patch.object(verifier, "_cleanup_uid", return_value=bad):
                with self.assertRaisesRegex(
                    verifier.VerifierControllerError, "proven quiescent"
                ):
                    verifier.run_verifier(
                        snapshot_root=paths["snapshot"],
                        controller_dir=paths["controller"],
                        runtime_root=paths["runtime"],
                        dependency_root=paths["dependency"],
                        archon_executable=paths["archon"],
                        lake_executable=paths["lake"],
                        verifier_user="ichoblindgptv",
                        scratch_root=paths["scratch"],
                        output=paths["controller"] / "residual.json",
                        scope_ids=["icho_t1_a1"], timeout_s=10,
                    )

    @unittest.skipUnless(os.geteuid() == 0, "controller test requires root")
    def test_root_runner_rejects_archon_outside_sealed_runtime(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paths = self._fixture(root)
            external = root / "external-archon"
            external.write_bytes(paths["archon"].read_bytes())
            external.chmod(0o755)
            with self.assertRaisesRegex(
                verifier.VerifierControllerError, "inside the sealed runtime"
            ):
                verifier.run_verifier(
                    snapshot_root=paths["snapshot"],
                    controller_dir=paths["controller"],
                    runtime_root=paths["runtime"],
                    dependency_root=paths["dependency"],
                    archon_executable=external,
                    lake_executable=paths["lake"],
                    verifier_user="ichoblindgptv", scratch_root=paths["scratch"],
                    output=paths["controller"] / "outside.json",
                    scope_ids=["icho_t1_a1"], timeout_s=10,
                )

    @unittest.skipUnless(os.geteuid() == 0, "controller test requires root")
    def test_root_runner_rejects_archon_outside_runtime_inventory(self):
        with tempfile.TemporaryDirectory() as td:
            paths = self._fixture(Path(td))
            outside = Path(td) / "outside-archon"
            outside.write_bytes(paths["archon"].read_bytes())
            outside.chmod(0o755)
            with self.assertRaisesRegex(
                verifier.VerifierControllerError, "inside the sealed runtime",
            ):
                verifier.run_verifier(
                    snapshot_root=paths["snapshot"],
                    controller_dir=paths["controller"],
                    runtime_root=paths["runtime"],
                    dependency_root=paths["dependency"],
                    archon_executable=outside, lake_executable=paths["lake"],
                    verifier_user="ichoblindgptv", scratch_root=paths["scratch"],
                    output=paths["controller"] / "outside.json",
                    scope_ids=["icho_t1_a1"], timeout_s=10,
                )


if __name__ == "__main__":
    unittest.main()
