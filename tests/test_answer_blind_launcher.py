from __future__ import annotations

import importlib.util
import json
import os
import pwd
import shutil
import stat
import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_answer_blind_iteration.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_launcher", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def _identity() -> object:
    for name in ("ichoblindgpt", "ichoblindk3", "nobody"):
        try:
            entry = pwd.getpwnam(name)
        except KeyError:
            continue
        if entry.pw_uid and not MODULE._real_uid_pids(entry.pw_uid):
            return MODULE.SolverIdentity(name, entry.pw_uid, entry.pw_gid)
    raise unittest.SkipTest("no quiescent dedicated non-root test UID")


@unittest.skipUnless(os.geteuid() == 0 and shutil.which("gcc"), "root and gcc required")
class RealKernelLandlockTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if MODULE.landlock_abi() < 4:
            raise unittest.SkipTest("Landlock ABI 4 required")
        cls.identity = _identity()
        cls.base = Path(tempfile.mkdtemp(prefix="answer-blind-launcher-", dir="/var/lib"))
        os.chmod(cls.base, 0o755)
        cls.helper = cls.base / "helper"
        subprocess.run(
            ["gcc", "-static", "-O2", str(ROOT / "tests/fixtures/answer_blind_landlock_helper.c"), "-o", str(cls.helper)],
            check=True,
        )
        os.chown(cls.helper, 0, 0)
        os.chmod(cls.helper, 0o555)

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.base)

    def _run(self, argv: list[str], policy: object, name: str) -> object:
        return MODULE.run_confined_command(
            argv=argv,
            cwd=self.base,
            environment={"PATH": ""},
            identity=self.identity,
            policy=policy,
            log_path=self.base / f"{name}.log",
            timeout_s=5,
            rlimit_nproc=32,
        )

    def test_regular_writable_file_rule_works_on_kernel(self) -> None:
        target = self.base / "state"
        target.touch(mode=0o600)
        os.chown(target, self.identity.uid, self.identity.gid)
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(),
            read_only_paths=(self.helper,),
            read_write_paths=(target,),
            probe_paths=(Path("/root"),),
        )
        result = self._run([str(self.helper), "write", str(target)], policy, "write")
        self.assertEqual(result.exit_code, 0)
        self.assertIsNone(result.confinement_error)
        self.assertEqual(target.read_text(), "ok\n")

    def test_probe_failure_exits_before_payload_exec(self) -> None:
        marker = self.base / "must-not-exist"
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(),
            read_only_paths=(self.helper, self.base),
            read_write_paths=(self.base,),
            # This path is deliberately authorized, so the negative probe must
            # fail and preexec must exit 126 before helper writes the marker.
            probe_paths=(self.base,),
        )
        result = self._run([str(self.helper), "write", str(marker)], policy, "probe")
        self.assertEqual(result.exit_code, 126)
        self.assertIsNotNone(result.confinement_error)
        self.assertFalse(marker.exists())

    def test_double_fork_setsid_cannot_survive_uid_quiescence(self) -> None:
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(),
            read_only_paths=(self.helper,),
            read_write_paths=(),
            probe_paths=(Path("/root"),),
        )
        result = self._run([str(self.helper), "double-fork"], policy, "double-fork")
        self.assertEqual(MODULE._real_uid_pids(self.identity.uid), [])
        self.assertTrue(result.dedicated_uid_quiescence["quiescent_after"])
        if result.dedicated_uid_quiescence["prlimit_zero_applied"] is False:
            self.assertIsNotNone(result.confinement_error)

    def test_tcp_only_broker_port_allowed_and_other_tcp_denied(self) -> None:
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listener.bind(("127.0.0.1", 0))
        listener.listen(2)
        allowed_port = listener.getsockname()[1]
        denied = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        denied.bind(("127.0.0.1", 0))
        denied.listen(1)
        denied_port = denied.getsockname()[1]
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(), read_only_paths=(self.helper,),
            read_write_paths=(), probe_paths=(Path("/root"),),
            allowed_connect_tcp_ports=(allowed_port,),
        )
        try:
            allowed = self._run(
                [str(self.helper), "tcp", str(allowed_port)], policy, "tcp-allowed"
            )
            blocked = self._run(
                [str(self.helper), "tcp", str(denied_port)], policy, "tcp-denied"
            )
        finally:
            listener.close()
            denied.close()
        self.assertEqual(allowed.exit_code, 0)
        self.assertEqual(blocked.exit_code, 41)

    def test_udp_socket_is_denied_by_seccomp(self) -> None:
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(), read_only_paths=(self.helper,),
            read_write_paths=(), probe_paths=(Path("/root"),),
        )
        result = self._run([str(self.helper), "udp"], policy, "udp-denied")
        self.assertEqual(result.exit_code, 0)

    def test_mptcp_socket_is_denied_by_seccomp(self) -> None:
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(), read_only_paths=(self.helper,),
            read_write_paths=(), probe_paths=(Path("/root"),),
        )
        result = self._run([str(self.helper), "mptcp"], policy, "mptcp-denied")
        self.assertEqual(result.exit_code, 0)

    def test_io_uring_setup_is_denied_by_seccomp(self) -> None:
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(), read_only_paths=(self.helper,),
            read_write_paths=(), probe_paths=(Path("/root"),),
        )
        result = self._run([str(self.helper), "io-uring"], policy, "io-uring-denied")
        self.assertEqual(result.exit_code, 0)

    def test_pathname_unix_socket_is_denied_by_seccomp(self) -> None:
        socket_path = self.base / "host-path.sock"
        listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        listener.bind(str(socket_path))
        listener.listen(1)
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(), read_only_paths=(self.helper,),
            read_write_paths=(), probe_paths=(Path("/root"),),
        )
        try:
            result = self._run(
                [str(self.helper), "unix-path", str(socket_path)],
                policy,
                "unix-path-denied",
            )
        finally:
            listener.close()
        self.assertEqual(result.exit_code, 0)

    def test_abstract_unix_socket_and_socketpair_are_denied(self) -> None:
        abstract_name = f"answer-blind-{os.getpid()}-{id(self)}"
        listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        listener.bind("\0" + abstract_name)
        listener.listen(1)
        policy = MODULE.LandlockPolicy(
            abi=MODULE.landlock_abi(), read_only_paths=(self.helper,),
            read_write_paths=(), probe_paths=(Path("/root"),),
        )
        try:
            abstract = self._run(
                [str(self.helper), "unix-abstract", abstract_name],
                policy,
                "unix-abstract-denied",
            )
            pair = self._run(
                [str(self.helper), "socketpair"], policy, "socketpair-denied"
            )
        finally:
            listener.close()
        self.assertEqual(abstract.exit_code, 0)
        self.assertEqual(pair.exit_code, 0)


class CleanSnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        self.base = Path(tempfile.mkdtemp(prefix="answer-blind-snapshot-", dir="/var/lib"))
        self.source = self.base / "source"
        self.destination = self.base / "snapshot"
        self.dependency = self.base / "dependency"
        self.source.mkdir()
        self.dependency.mkdir()
        (self.dependency / "dep.txt").write_text("sealed")
        (self.source / "reports/x").mkdir(parents=True)
        (self.source / "IChO2026Problems").mkdir()
        (self.source / "blind_candidates").mkdir()
        (self.source / ".lake/build").mkdir(parents=True)
        (self.source / ".lake/config").mkdir()
        (self.source / ".lake/packages").symlink_to(self.dependency)
        for record_id in ("icho_2026_t1_a1", "icho_2026_t1_a2"):
            target = f"IChO2026Problems/problem_{record_id}.lean"
            (self.source / target).write_text(f"theorem {record_id} : True := by trivial\n")
            report = {"entry": {"id": record_id}, "output_lean": target}
            (self.source / f"reports/x/{record_id}.source.json").write_text(json.dumps(report))
            (self.source / f"blind_candidates/{record_id}.json").write_text("{}")
        (self.source / ".lake/build/Evil.olean").write_bytes(b"malicious")
        (self.source / "IChO2026Problems/Shadow.olean").write_bytes(b"malicious")

    def tearDown(self) -> None:
        shutil.rmtree(self.base)

    def test_clean_snapshot_drops_build_olean_and_scopes_reports(self) -> None:
        MODULE._copy_clean_snapshot(
            source=self.source,
            destination=self.destination,
            dependency=self.dependency.resolve(),
            scope_ids=["icho_2026_t1_a1"],
        )
        self.assertFalse((self.destination / ".lake/build").exists())
        self.assertFalse((self.destination / ".lake/config").exists())
        self.assertEqual(list(self.destination.rglob("*.olean")), [])
        reports = list((self.destination / "reports").rglob("*.source.json"))
        self.assertEqual([path.stem for path in reports], ["icho_2026_t1_a1.source"])
        umbrella = (self.destination / "IChO2026Problems/All.lean").read_text()
        self.assertIn("import IChO2026Problems.problem_icho_2026_t1_a1", umbrella)
        self.assertNotIn("t1_a2", umbrella)
        inventory = MODULE._snapshot_inventory(
            self.destination, dependency=self.dependency.resolve()
        )
        self.assertNotIn(".lake/packages", inventory)

    def test_inventory_rejects_escaping_symlink(self) -> None:
        root = self.base / "inventory"
        root.mkdir()
        (root / "escape").symlink_to(self.dependency / "dep.txt")
        with self.assertRaises(MODULE.ControllerError):
            MODULE._inventory_tree(root)


class SchemaTests(unittest.TestCase):
    def test_protocol_is_shared_with_model_broker(self) -> None:
        broker_script = ROOT / "scripts/run_answer_blind_model_broker.py"
        broker_spec = importlib.util.spec_from_file_location("answer_blind_broker_schema", broker_script)
        assert broker_spec and broker_spec.loader
        broker = importlib.util.module_from_spec(broker_spec)
        sys.modules[broker_spec.name] = broker
        broker_spec.loader.exec_module(broker)
        self.assertEqual(MODULE.PROTOCOL, broker.PROTOCOL)

    def test_finalize_cli_is_closed_and_requires_broker_evidence(self) -> None:
        parser = MODULE._parser()
        with self.assertRaises(SystemExit):
            parser.parse_args(["finalize"])
        help_text = parser._subparsers._group_actions[0].choices["finalize"].format_help()
        self.assertIn("--model-broker-transcript", help_text)
        self.assertIn("--quarantine-workspace", help_text)
        self.assertIn("--verifier-user", help_text)


if __name__ == "__main__":
    unittest.main()
