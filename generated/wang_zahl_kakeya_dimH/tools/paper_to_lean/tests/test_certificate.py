from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parents[1]
PROJECT = TOOLS.parents[1]
sys.path.insert(0, str(TOOLS))

import certificate as production  # noqa: E402


class ProductionCertificateTests(unittest.TestCase):
    def test_provenance_payload_cannot_escape_comment(self) -> None:
        payload = (
            "-/\n"
            "axiom injectedFalse : False\n"
            "macro_rules | `(tactic| omega) => "
            "`(tactic| exact False.elim injectedFalse)\n"
            "/-"
        )
        model = production.ValidModel(
            name="fabricated",
            namespace="InjectedAudit",
            variables=["x"],
            constraints=[],
            claim=False,
        )
        source, _ = production.generate_lean(
            model,
            "unsat",
            {},
            {
                "path": "fixture",
                "locator": payload,
                "sha256": "0" * 64,
                "url": None,
            },
        )
        self.assertNotIn("\naxiom injectedFalse", source)
        self.assertNotIn("\nmacro_rules", source)
        checked = subprocess.run(
            ["lake", "env", "lean", "-E", "warning", "--stdin"],
            cwd=PROJECT,
            input=source,
            text=True,
            capture_output=True,
            check=False,
            timeout=120,
        )
        self.assertNotEqual(checked.returncode, 0)
        self.assertNotIn("depends on axioms: [injectedFalse]", checked.stdout)

    def test_axiom_audit_is_unique_and_bound_to_target(self) -> None:
        target = "N.good"
        standard = (
            "'N.good' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
        )
        ok, axioms, error = production.audit_axioms(standard, target)
        self.assertTrue(ok)
        self.assertEqual(set(axioms), production.ALLOWED_AXIOMS)
        self.assertIsNone(error)

        wrong = "diagnostic: helper does not depend on any axioms\n"
        self.assertFalse(production.audit_axioms(wrong, target)[0])

        other = "'N.other' does not depend on any axioms\n"
        self.assertFalse(production.audit_axioms(other, target)[0])

        doubled = standard + "'N.other' does not depend on any axioms\n"
        self.assertFalse(production.audit_axioms(doubled, target)[0])

        injected = "'N.good' depends on axioms: [injectedFalse]\n"
        self.assertFalse(production.audit_axioms(injected, target)[0])

        independent = "'N.good' does not depend on any axioms\n"
        self.assertTrue(production.audit_axioms(independent, target)[0])

    def test_source_hash_and_root_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "root"
            root.mkdir()
            manifest = root / "manifest.json"
            manifest.write_text("{}", encoding="utf-8")
            source_file = root / "source.txt"
            excerpt = "PINNED\n"
            source_file.write_text(excerpt, encoding="utf-8")
            source = {
                "path": "source.txt",
                "start_line": 1,
                "end_line": 1,
                "expected_sha256": hashlib.sha256(excerpt.encode()).hexdigest(),
            }
            snapshot = production.extract_source_snapshot(manifest, root, source)
            self.assertEqual(snapshot.excerpt, excerpt)

            mismatch = dict(source, expected_sha256="0" * 64)
            with self.assertRaises(production.SecureManifestError):
                production.extract_source_snapshot(manifest, root, mismatch)

            absolute = dict(source, path=str(source_file))
            with self.assertRaises(production.SecureManifestError):
                production.extract_source_snapshot(manifest, root, absolute)

            outside = Path(temporary) / "outside.txt"
            outside.write_text(excerpt, encoding="utf-8")
            traversal = dict(source, path="../outside.txt")
            with self.assertRaises(production.SecureManifestError):
                production.extract_source_snapshot(manifest, root, traversal)

            link = root / "outside-link.txt"
            try:
                link.symlink_to(outside)
            except OSError:
                pass
            else:
                linked = dict(source, path="outside-link.txt")
                with self.assertRaises(production.SecureManifestError):
                    production.extract_source_snapshot(manifest, root, linked)

    def test_manifest_and_model_schema_are_strict_and_typed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "manifest.json"
            path.write_text('{"model": {}}', encoding="utf-8")
            with self.assertRaises(production.SecureManifestError):
                production.read_manifest_once(path)
            path.write_text(
                '{"source": {}, "model": {}, "souce": {}}', encoding="utf-8"
            )
            with self.assertRaises(production.SecureManifestError):
                production.read_manifest_once(path)
            path.write_text(
                '{"source": {}, "model": {}, "model": {"name": "shadow"}}',
                encoding="utf-8",
            )
            with self.assertRaises(production.SecureManifestError):
                production.read_manifest_once(path)

        ill_typed = {
            "name": "badSort",
            "variables": ["x"],
            "constraints": [{"op": "and", "args": ["x"]}],
            "claim": True,
        }
        with self.assertRaises(production.SecureManifestError):
            production.validate_model(ill_typed)

        reserved = {
            "name": "theorem",
            "variables": ["x"],
            "constraints": [],
            "claim": True,
        }
        with self.assertRaises(production.SecureManifestError):
            production.validate_model(reserved)

        for keyword in ("mutual", "section", "macro_rules", "elab", "as"):
            blocked = {
                "name": keyword,
                "variables": ["x"],
                "constraints": [],
                "claim": True,
            }
            with self.subTest(keyword=keyword):
                with self.assertRaises(production.SecureManifestError):
                    production.validate_model(blocked)

    def test_nul_paths_are_rejected_as_manifest_errors(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest = root / "manifest.json"
            manifest.write_text("{}", encoding="utf-8")
            source = {
                "path": "bad\x00path",
                "start_line": 1,
                "end_line": 1,
                "expected_sha256": "0" * 64,
            }
            with self.assertRaises(production.SecureManifestError):
                production.extract_source_snapshot(manifest, root, source)
            with self.assertRaises(production.SecureManifestError):
                production.resolve_existing_path("bad\x00path", "test path")

    def test_render_growth_is_bounded_before_generation(self) -> None:
        atom = {"op": "eq", "args": ["x", 0]}
        nested = atom
        for _ in range(100):
            nested = {"op": "xor", "args": [nested, False]}
        model = production.validate_model(
            {
                "name": "linearXor",
                "variables": ["x"],
                "constraints": [],
                "claim": nested,
            }
        )
        rendered = production.lean_term(model.claim)
        self.assertLess(len(rendered), 10_000)

        variables = [f"x{index}" for index in range(65)]
        too_wide = {
            "name": "wideDistinct",
            "variables": variables,
            "constraints": [],
            "claim": {"op": "distinct", "args": variables},
        }
        with self.assertRaises(production.SecureManifestError):
            production.validate_model(too_wide)

        allowed_variables = variables[: production.MAX_DISTINCT_ARITY]
        costly = {"op": "distinct", "args": allowed_variables}
        over_budget = {
            "name": "manyDistinct",
            "variables": allowed_variables,
            "constraints": [costly] * 130,
            "claim": True,
        }
        with self.assertRaises(production.SecureManifestError):
            production.validate_model(over_budget)

    def test_bounded_reader_rejects_oversize_before_loading(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "sparse"
            with path.open("wb") as stream:
                stream.truncate(production.MAX_MANIFEST_BYTES + 1)
            with self.assertRaises(production.SecureManifestError):
                production.read_bytes_bounded(
                    path, production.MAX_MANIFEST_BYTES, "manifest"
                )

    def test_process_group_timeout_leaves_no_running_child(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            child_pid_file = Path(temporary) / "child.pid"
            command = (
                "sleep 30 & "
                + "echo $! > "
                + str(child_pid_file)
                + "; wait"
            )
            with self.assertRaises(production.SecureManifestError):
                production.run_process(
                    ["/bin/sh", "-c", command],
                    timeout=1,
                    label="test process tree",
                )
            child_pid = int(child_pid_file.read_text(encoding="utf-8"))
            alive = True
            for _ in range(40):
                proc_stat = Path(f"/proc/{child_pid}/stat")
                if not proc_stat.exists():
                    alive = False
                    break
                fields = proc_stat.read_text(encoding="utf-8").split()
                if len(fields) > 2 and fields[2] == "Z":
                    alive = False
                    break
                time.sleep(0.05)
            self.assertFalse(alive, "timed-out child process is still running")

    def test_real_sat_counterexample_is_checked_by_lean(self) -> None:
        z3 = shutil.which("z3")
        if z3 is None:
            self.skipTest("z3 is not installed")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source_file = directory / "source.txt"
            excerpt = "PIN\n"
            source_file.write_text(excerpt, encoding="utf-8")
            manifest = directory / "manifest.json"
            manifest.write_text(
                json.dumps(
                    {
                        "source": {
                            "path": "source.txt",
                            "start_line": 1,
                            "end_line": 1,
                            "expected_sha256": hashlib.sha256(
                                excerpt.encode()
                            ).hexdigest(),
                        },
                        "model": {
                            "name": "disprovedClaim",
                            "namespace": "RealSatAudit",
                            "variables": ["x"],
                            "constraints": [
                                {"op": "eq", "args": ["x", 0]}
                            ],
                            "claim": {"op": "eq", "args": ["x", 1]},
                        },
                    }
                ),
                encoding="utf-8",
            )
            output = directory / "artifacts"
            args = argparse.Namespace(
                manifest=str(manifest),
                output=str(output),
                project=str(PROJECT),
                source_root=None,
                z3=z3,
                lake="lake",
                z3_timeout=10,
                lean_timeout=120,
            )
            self.assertEqual(production.run(args), 0)
            report = json.loads(
                (output / "report.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                report["solver_status_for_constraints_and_not_claim"], "sat"
            )
            self.assertEqual(report["counterexample"], {"x": 0})
            self.assertTrue(report["lean_verified"])
            self.assertTrue(
                report["certificate_theorem"].endswith("_counterexample")
            )

    def test_false_unsat_from_fake_solver_is_rejected_by_lean(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source_file = directory / "source.txt"
            excerpt = "PIN\n"
            source_file.write_text(excerpt, encoding="utf-8")
            manifest = directory / "manifest.json"
            manifest.write_text(
                """
{
  "source": {
    "path": "source.txt",
    "start_line": 1,
    "end_line": 1,
    "expected_sha256": "%s"
  },
  "model": {
    "name": "falseClaim",
    "namespace": "FakeSolverAudit",
    "variables": ["x"],
    "constraints": [],
    "claim": false
  }
}
""" % hashlib.sha256(excerpt.encode()).hexdigest(),
                encoding="utf-8",
            )
            fake_z3 = directory / "fake-z3"
            fake_z3.write_text("#!/bin/sh\nprintf 'unsat\\n'\n", encoding="utf-8")
            fake_z3.chmod(0o700)
            output = directory / "artifacts"
            args = argparse.Namespace(
                manifest=str(manifest),
                output=str(output),
                project=str(PROJECT),
                source_root=None,
                z3=str(fake_z3),
                lake="lake",
                z3_timeout=10,
                lean_timeout=120,
            )
            self.assertEqual(production.run(args), 2)
            report = (output / "report.json").read_text(encoding="utf-8")
            self.assertIn('"lean_verified": false', report)
            self.assertIn('"lean_returncode": 1', report)


if __name__ == "__main__":
    unittest.main()
