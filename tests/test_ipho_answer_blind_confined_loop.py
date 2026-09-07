from __future__ import annotations

import errno
import hashlib
import importlib.util
import os
import signal
import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_ipho_answer_blind_confined_loop.py"
)
SPEC = importlib.util.spec_from_file_location("ipho_confined_loop", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


@dataclass(frozen=True)
class FakePolicy:
    abi: int
    read_only_paths: tuple[Path, ...]
    read_write_paths: tuple[Path, ...]
    probe_paths: tuple[Path, ...]
    allowed_connect_tcp_ports: tuple[int, ...]


class IphoConfinedLoopTests(unittest.TestCase):
    def test_claude_tokio_pool_is_single_threaded(self):
        self.assertEqual(MODULE.TOKIO_WORKER_THREADS, "1")

    def _minimal_hf_cache(
        self, root: Path, *, revision: str = "a" * 40
    ) -> tuple[Path, dict[str, str], dict[str, str]]:
        cache = root / "hf-cache"
        model = cache / "hub" / MODULE.LEAN_EXPLORE_EMBEDDING_CACHE_REPO
        snapshot = model / "snapshots" / revision
        for directory in (model / "blobs", model / "refs", snapshot):
            directory.mkdir(parents=True, exist_ok=True)
        (model / "refs" / "main").write_text(revision, encoding="ascii")
        snapshot_blobs = {
            name: f"blob-{index}"
            for index, name in enumerate(
                (
            "config.json",
            "model.safetensors",
            "modules.json",
            "tokenizer.json",
            "tokenizer_config.json",
                )
            )
        }
        expected_blobs: dict[str, str] = {}
        for relative, blob_name in snapshot_blobs.items():
            payload = f"cached-{blob_name}".encode("ascii")
            blob = model / "blobs" / blob_name
            blob.write_bytes(payload)
            expected_blobs[blob_name] = hashlib.sha256(payload).hexdigest()
            os.link(blob, snapshot / relative)
        return cache, expected_blobs, snapshot_blobs

    def test_creates_ipho_only_compatibility_anchors_for_sealed_helper(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = Path(raw)
            source = workspace / "IPhO2026Problems.lean"
            source.write_text("import IPhO2026Problems.All\n", encoding="utf-8")
            method = MODULE._ensure_legacy_umbrella_anchor(workspace)
            self.assertIn("legacy-target-all", method)
            self.assertEqual(
                (workspace / "IChO2026Problems.lean").read_bytes(),
                source.read_bytes(),
            )
            self.assertEqual(
                (workspace / "IChO2026Problems/All.lean").read_text(
                    encoding="utf-8"
                ),
                "import IPhO2026Problems\n\n"
                "/-! Sealed-helper compatibility anchor. -/\n",
            )

    def test_parameterizes_only_mutable_target_paths(self):
        sealed = SimpleNamespace(
            MUTABLE_WORKSPACE_DIRS=(
                "IChO2026Problems",
                "blind_candidates",
                "blueprint",
                ".lake/build",
                ".lake/config",
                ".archon/logs",
            ),
            MUTABLE_WORKSPACE_FILES=(
                "IChO2026Problems/All.lean",
                ".archon/PROGRESS.md",
            ),
        )
        MODULE._parameterize_ipho_targets(sealed)
        self.assertEqual(sealed.MUTABLE_WORKSPACE_DIRS[0], "IPhO2026Problems")
        self.assertEqual(
            sealed.MUTABLE_WORKSPACE_FILES,
            ("IPhO2026Problems/All.lean", ".archon/PROGRESS.md"),
        )
        self.assertIn("blueprint", sealed.MUTABLE_WORKSPACE_DIRS)
        self.assertIn(".lake/build", sealed.MUTABLE_WORKSPACE_DIRS)

    def test_broker_binding_is_exact_model_dummy_and_loopback(self):
        base_url = "http://127.0.0.1:39421"
        credentials = {
            "ANTHROPIC_BASE_URL": base_url,
            "ANTHROPIC_AUTH_TOKEN": MODULE.DUMMY_TOKEN,
        }
        receipt = {
            "phase": "model_broker_ready",
            "run_id": "ipho-run-1",
            "allowed_model": MODULE.MODEL,
            "listen_url": base_url,
            "request_profile": MODULE.BROKER_REQUEST_PROFILE,
            "public_dummy_key_sha256": hashlib.sha256(
                MODULE.DUMMY_TOKEN.encode()
            ).hexdigest(),
        }
        self.assertEqual(
            MODULE._validate_broker_binding(
                receipt, credentials, run_id="ipho-run-1"
            ),
            39421,
        )
        with self.assertRaisesRegex(MODULE.LaunchError, "run/model/URL"):
            MODULE._validate_broker_binding(
                {**receipt, "allowed_model": "other-model"},
                credentials,
                run_id="ipho-run-1",
            )
        with self.assertRaisesRegex(MODULE.LaunchError, "IPv4 loopback"):
            MODULE._validate_broker_binding(
                {**receipt, "listen_url": "https://api.example/v1"},
                {**credentials, "ANTHROPIC_BASE_URL": "https://api.example/v1"},
                run_id="ipho-run-1",
            )

    def test_command_and_policy_keep_authority_narrow(self):
        argv = MODULE._archon_argv(
            Path("/sealed/bin/archon"),
            max_iterations=7,
            max_parallel=4,
            max_objectives=28,
        )
        self.assertEqual(
            argv[:8],
            (
                "/sealed/venv/bin/python",
                "-P",
                "-c",
                MODULE.ARCHON_FORK_BOOTSTRAP,
                "loop",
                ".",
                "--from",
                "prover",
            ),
        )
        self.assertIn("--formalization-review-gate", argv)
        self.assertIn("--proof-review-gate", argv)
        self.assertEqual(
            argv[argv.index("--proof-review-max-iterations") + 1], "7"
        )
        self.assertEqual(argv[-2:], ("--model", MODULE.MODEL))
        self.assertFalse(any("answer" in item.casefold() for item in argv))

        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            supplemental = root / "supplemental"
            readonly = root / "readonly"
            writable = root / "writable"
            for path in (supplemental, readonly, writable):
                path.mkdir()
            sealed = SimpleNamespace(LandlockPolicy=FakePolicy)
            original = FakePolicy(
                abi=6,
                read_only_paths=(readonly,),
                read_write_paths=(writable,),
                probe_paths=(Path("/root"),),
                allowed_connect_tcp_ports=(39421,),
            )
            extended = MODULE._extend_readonly_policy(
                sealed, original, supplemental
            )
            self.assertEqual(
                extended.read_only_paths, (readonly, supplemental)
            )
            self.assertEqual(extended.read_write_paths, (writable,))
            self.assertEqual(extended.allowed_connect_tcp_ports, (39421,))

    def test_promotes_only_exact_dev_null_to_writable(self):
        sealed = SimpleNamespace(LandlockPolicy=FakePolicy)
        original = FakePolicy(
            abi=6,
            read_only_paths=(Path("/dev/null"), Path("/dev/zero")),
            read_write_paths=(Path("/tmp/private"),),
            probe_paths=(Path("/root"),),
            allowed_connect_tcp_ports=(39421,),
        )

        promoted = MODULE._promote_dev_null_writable(sealed, original)

        self.assertEqual(promoted.read_only_paths, (Path("/dev/zero"),))
        self.assertEqual(
            promoted.read_write_paths,
            (Path("/tmp/private"), Path("/dev/null")),
        )
        self.assertNotIn(Path("/dev"), promoted.read_write_paths)

    def test_promotes_exact_dev_shm_for_process_pool(self):
        sealed = SimpleNamespace(LandlockPolicy=FakePolicy)
        original = FakePolicy(
            abi=6,
            read_only_paths=(Path("/dev/zero"),),
            read_write_paths=(Path("/dev/null"), Path("/tmp/private")),
            probe_paths=(Path("/root"), Path("/dev/shm")),
            allowed_connect_tcp_ports=(39421,),
        )

        promoted = MODULE._promote_dev_shm_writable(sealed, original)

        self.assertEqual(promoted.read_only_paths, (Path("/dev/zero"),))
        self.assertEqual(
            promoted.read_write_paths,
            (Path("/dev/null"), Path("/tmp/private"), Path("/dev/shm")),
        )
        self.assertEqual(promoted.probe_paths, (Path("/root"),))
        self.assertNotIn(Path("/dev"), promoted.read_write_paths)

    def test_validates_only_one_materialized_qwen_embedding_cache(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            cache, expected_blobs, snapshot_blobs = self._minimal_hf_cache(root)
            validator_options = {
                "expected_revision": "a" * 40,
                "expected_blobs": expected_blobs,
                "expected_snapshot_blobs": snapshot_blobs,
                "expected_missing_markers": set(),
            }
            inventory = MODULE._validate_lean_explore_hf_cache(
                cache, **validator_options
            )
            self.assertEqual(
                inventory["model"], "Qwen/Qwen3-Embedding-0.6B"
            )
            self.assertEqual(inventory["revision"], "a" * 40)
            self.assertGreaterEqual(inventory["files"], 6)

            unrelated = cache / "hub" / "datasets--private--answers"
            unrelated.mkdir()
            with self.assertRaisesRegex(MODULE.LaunchError, "must contain only"):
                MODULE._validate_lean_explore_hf_cache(cache, **validator_options)
            unrelated.rmdir()

            snapshot = (
                cache
                / "hub"
                / MODULE.LEAN_EXPLORE_EMBEDDING_CACHE_REPO
                / "snapshots"
                / ("a" * 40)
            )
            (snapshot / "answers.json").write_text("not allowed", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.LaunchError, "snapshot manifest"):
                MODULE._validate_lean_explore_hf_cache(cache, **validator_options)
            (snapshot / "answers.json").unlink()

            blob = (
                cache
                / "hub"
                / MODULE.LEAN_EXPLORE_EMBEDDING_CACHE_REPO
                / "blobs"
                / "blob-0"
            )
            blob.write_bytes(b"tampered")
            with self.assertRaisesRegex(MODULE.LaunchError, "blob digest differs"):
                MODULE._validate_lean_explore_hf_cache(cache, **validator_options)

    def test_rejects_symlinks_and_unreadable_hf_cache_entries(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            cache, _, _ = self._minimal_hf_cache(root)
            snapshot = (
                cache
                / "hub"
                / MODULE.LEAN_EXPLORE_EMBEDDING_CACHE_REPO
                / "snapshots"
                / ("a" * 40)
            )
            link = snapshot / "README.md"
            link.symlink_to("config.json")
            with self.assertRaisesRegex(MODULE.LaunchError, "unsupported entry"):
                MODULE._validate_lean_explore_hf_cache(cache)
            link.unlink()
            (snapshot / "config.json").chmod(0o640)
            with self.assertRaisesRegex(MODULE.LaunchError, "solver-readable"):
                MODULE._validate_lean_explore_hf_cache(cache)

    def test_hf_cache_is_exact_readonly_authority_and_offline_environment(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            hf_cache = root / "hf-cache"
            supplemental = root / "supplemental"
            readonly = root / "readonly"
            writable = root / "writable"
            for path in (hf_cache, supplemental, readonly, writable):
                path.mkdir()
            sealed = SimpleNamespace(LandlockPolicy=FakePolicy)
            policy = FakePolicy(
                abi=6,
                read_only_paths=(readonly,),
                read_write_paths=(writable,),
                probe_paths=(Path("/root"),),
                allowed_connect_tcp_ports=(39421,),
            )
            policy = MODULE._extend_readonly_policy(
                sealed, policy, supplemental, label="supplemental"
            )
            policy = MODULE._extend_readonly_policy(
                sealed, policy, hf_cache, label="HF cache"
            )
            self.assertEqual(
                policy.read_only_paths, (readonly, supplemental, hf_cache)
            )
            self.assertNotIn(hf_cache.parent, policy.read_only_paths)

            probe_policy = FakePolicy(
                abi=6,
                read_only_paths=(readonly,),
                read_write_paths=(writable,),
                probe_paths=(hf_cache / "must-remain-denied",),
                allowed_connect_tcp_ports=(39421,),
            )
            with self.assertRaisesRegex(MODULE.LaunchError, "denial probe"):
                MODULE._extend_readonly_policy(
                    sealed, probe_policy, hf_cache, label="HF cache"
                )

            environment = MODULE._lean_explore_hf_environment(hf_cache)
            self.assertEqual(environment["HF_HOME"], str(hf_cache))
            self.assertEqual(environment["HF_HUB_OFFLINE"], "1")
            self.assertEqual(environment["TRANSFORMERS_OFFLINE"], "1")

    def test_pinned_claude_runtime_and_narrow_policy(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            claude = root / "claude"
            payload = b"fixed-claude-test-binary"
            claude.write_bytes(payload)
            claude.chmod(0o555)
            runtime_ls = root / "ls"
            ls_payload = b"fixed-ls-test-binary"
            runtime_ls.write_bytes(ls_payload)
            runtime_ls.chmod(0o755)
            verified, runtime_paths = MODULE._validate_claude_runtime(
                claude,
                expected_sha256=hashlib.sha256(payload).hexdigest(),
                ls_binary=runtime_ls,
                ls_expected_sha256=hashlib.sha256(ls_payload).hexdigest(),
            )
            self.assertEqual(verified, claude.resolve())
            self.assertIn(runtime_ls.resolve(), runtime_paths)
            self.assertNotIn(runtime_ls.parent.resolve(), runtime_paths)
            self.assertIn(Path("/proc"), runtime_paths)

            readonly = root / "readonly"
            writable = root / "writable"
            readonly.mkdir()
            writable.mkdir()
            sealed = SimpleNamespace(LandlockPolicy=FakePolicy)
            policy = FakePolicy(
                abi=6,
                read_only_paths=(readonly,),
                read_write_paths=(writable,),
                probe_paths=(
                    Path("/root"),
                    Path("/proc/1/environ"),
                    Path("/proc/12345/environ"),
                ),
                allowed_connect_tcp_ports=(39421,),
            )
            extended = MODULE._extend_claude_runtime_policy(
                sealed,
                policy,
                claude=verified,
                runtime_paths=(Path("/proc"),),
            )
            self.assertIn(verified, extended.read_only_paths)
            self.assertIn(Path("/proc"), extended.read_only_paths)
            self.assertIn(Path("/proc/1/environ"), extended.probe_paths)
            self.assertIn(Path("/proc/12345/environ"), extended.probe_paths)

            unsafe_probe = FakePolicy(
                abi=6,
                read_only_paths=(readonly,),
                read_write_paths=(writable,),
                probe_paths=(Path("/proc/self/status"),),
                allowed_connect_tcp_ports=(39421,),
            )
            with self.assertRaisesRegex(MODULE.LaunchError, "denial probe"):
                MODULE._extend_claude_runtime_policy(
                    sealed,
                    unsafe_probe,
                    claude=verified,
                    runtime_paths=(Path("/proc"),),
                )

            with self.assertRaisesRegex(MODULE.LaunchError, "ls helper SHA-256 drift"):
                MODULE._validate_claude_runtime(
                    claude,
                    expected_sha256=hashlib.sha256(payload).hexdigest(),
                    ls_binary=runtime_ls,
                    ls_expected_sha256="0" * 64,
                )

    def test_seccomp_socketpair_exception_is_exact(self):
        sealed = MODULE._load_sealed_helper(MODULE.SEALED_RUNTIME)

        def denied(array, number):
            for index in range(len(array) - 1):
                current = array[index]
                following = array[index + 1]
                if (
                    int(current.code) == 0x15
                    and int(current.jt) == 0
                    and int(current.jf) == 1
                    and int(current.k) == number
                    and int(following.code) == 0x06
                    and int(following.k) == (0x00050000 | errno.EPERM)
                ):
                    return True
            return False

        original, _program = sealed._seccomp_filter_program()
        self.assertTrue(denied(original, 53))
        self.assertTrue(denied(original, 49))
        self.assertTrue(denied(original, 50))

        MODULE._allow_seccomp_socketpair(sealed)
        patched, _program = sealed._seccomp_filter_program()
        self.assertFalse(denied(patched, 53))
        self.assertTrue(denied(patched, 49))
        self.assertTrue(denied(patched, 50))
        MODULE._allow_seccomp_socketpair(sealed)

    def test_seccomp_native_socket_exception_is_exact(self):
        sealed = MODULE._load_sealed_helper(MODULE.SEALED_RUNTIME)
        errno_result = 0x00050000 | errno.EPERM
        user_notif = int(sealed.SECCOMP_RET_USER_NOTIF)

        def actions(array, number):
            matches = []
            for index in range(len(array) - 1):
                current = array[index]
                following = array[index + 1]
                if (
                    int(current.code) == 0x15
                    and int(current.jt) == 0
                    and int(current.jf) == 1
                    and int(current.k) == number
                    and int(following.code) == 0x06
                ):
                    matches.append(int(following.k))
            return matches

        original, _program = sealed._seccomp_filter_program()
        self.assertEqual(actions(original, 41), [user_notif])
        self.assertEqual(actions(original, 42), [user_notif])
        self.assertEqual(actions(original, 438), [errno_result])

        MODULE._allow_seccomp_socketpair(sealed)
        MODULE._allow_seccomp_native_sockets(sealed)
        patched, _program = sealed._seccomp_filter_program()
        self.assertEqual(actions(patched, 41), [])
        self.assertEqual(actions(patched, 42), [])
        self.assertEqual(actions(patched, 438), [user_notif])
        self.assertEqual(actions(patched, 49), [errno_result])
        self.assertEqual(actions(patched, 50), [errno_result])
        self.assertEqual(actions(patched, 53), [])

        snapshot = [
            (int(item.code), int(item.jt), int(item.jf), int(item.k))
            for item in patched
        ]
        MODULE._allow_seccomp_native_sockets(sealed)
        repeated, _program = sealed._seccomp_filter_program()
        self.assertEqual(
            snapshot,
            [
                (int(item.code), int(item.jt), int(item.jf), int(item.k))
                for item in repeated
            ],
        )

    def test_seccomp_receive_deadline_converts_alarm_to_eintr(self):
        receive_request = 1234

        def fake_ioctl(_fd, request, _argument):
            if request == receive_request:
                signal.raise_signal(signal.SIGALRM)
            return 17

        sealed = SimpleNamespace(
            _seccomp_ioctl=fake_ioctl,
            SECCOMP_IOCTL_NOTIF_RECV=receive_request,
        )
        previous_handler = signal.getsignal(signal.SIGALRM)
        MODULE._install_seccomp_receive_deadline(sealed)
        with self.assertRaises(OSError) as raised:
            sealed._seccomp_ioctl(9, receive_request, object())
        self.assertEqual(raised.exception.errno, errno.EINTR)
        self.assertEqual(signal.getsignal(signal.SIGALRM), previous_handler)
        self.assertEqual(signal.getitimer(signal.ITIMER_REAL), (0.0, 0.0))
        self.assertEqual(sealed._seccomp_ioctl(9, 9999, object()), 17)


if __name__ == "__main__":
    unittest.main()
