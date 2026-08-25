from __future__ import annotations

import dataclasses
import hashlib
import importlib.util
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from PIL import Image


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_answer_blind_archon_isolated_campaign.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_archon_isolated", SCRIPT)
assert SPEC and SPEC.loader
RUNNER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = RUNNER
SPEC.loader.exec_module(RUNNER)


class IsolatedCampaignTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="isolated-archon-")
        self.base = Path(self.temporary.name)
        self.config = RUNNER.Config(
            campaign_root=self.base / "campaign",
            seed_workspace=self.base / "seed",
            lake_packages=self.base / "packages",
            codex_home_template=self.base / "codex-template",
            runtime_root=self.base / "runtime",
            archon_bin=str(self.base / "runtime/bin/archon"),
            python_bin=self.base / "runtime/venv/bin/python",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_canonical_scope_is_exact_full32(self) -> None:
        self.assertEqual(len(RUNNER.CANONICAL_TARGET_IDS), 32)
        self.assertEqual(len(set(RUNNER.CANONICAL_TARGET_IDS)), 32)
        self.assertEqual(RUNNER.GLOBAL_MAX_PARALLEL, 4)
        self.assertEqual(RUNNER.PER_TARGET_MAX_PARALLEL, 1)

    def test_identity_plan_is_unique_and_stable(self) -> None:
        first = RUNNER._identity_plan(self.config)
        second = RUNNER._identity_plan(self.config)
        self.assertEqual(first, second)
        self.assertEqual(len({item.uid for item in first}), 32)
        self.assertEqual(len({item.gid for item in first}), 32)
        self.assertEqual(len({item.username for item in first}), 32)
        self.assertEqual(tuple(item.target_id for item in first), RUNNER.CANONICAL_TARGET_IDS)

    def test_reserved_uid_and_gid_reject_nss_aliases_before_cleanup(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        users = [
            mock.Mock(pw_name=item.username, pw_uid=item.uid)
            for item in identities
        ]
        groups = [
            mock.Mock(gr_name=item.groupname, gr_gid=item.gid, gr_mem=())
            for item in identities
        ]
        with (
            mock.patch.object(RUNNER, "_ensure_identity"),
            mock.patch.object(
                RUNNER.pwd, "getpwall",
                return_value=users + [
                    mock.Mock(pw_name="unexpected_alias", pw_uid=identities[0].uid)
                ],
            ),
            mock.patch.object(RUNNER.grp, "getgrall", return_value=groups),
        ):
            with self.assertRaisesRegex(RUNNER.CampaignError, "not uniquely bound"):
                RUNNER._ensure_identities(self.config, identities)

        with (
            mock.patch.object(RUNNER, "_ensure_identity"),
            mock.patch.object(RUNNER.pwd, "getpwall", return_value=users),
            mock.patch.object(
                RUNNER.grp, "getgrall",
                return_value=groups + [
                    mock.Mock(
                        gr_name="unexpected_alias", gr_gid=identities[0].gid,
                        gr_mem=(),
                    )
                ],
            ),
        ):
            with self.assertRaisesRegex(RUNNER.CampaignError, "not uniquely bound"):
                RUNNER._ensure_identities(self.config, identities)

    def test_native_runner_parameterization_is_one_by_one(self) -> None:
        target_id = RUNNER.CANONICAL_TARGET_IDS[0]
        native = RUNNER._base_target_config(self.config, target_id, seed=self.base / "one")
        self.assertEqual(native.expected_items, 1)
        self.assertEqual(native.max_parallel, 1)
        self.assertTrue(native.reuse_lake_packages)
        self.assertTrue(native.in_place_index)
        command = RUNNER.NATIVE.loop_command(native, resume=False)
        self.assertIn(
            ".lake/package-overrides.json",
            RUNNER._SEALED_WORKSPACE_PATHS,
        )
        self.assertEqual(command[command.index("--max-parallel") + 1], "1")
        self.assertEqual(command[command.index("--max-objectives") + 1], "1")

    def test_prepare_layout_normalizes_traversal_parents_under_umask_077(self) -> None:
        previous = os.umask(0o077)
        try:
            RUNNER._prepare_layout(self.config)
        finally:
            os.umask(previous)
        self.assertEqual(stat.S_IMODE(self.config.campaign_root.stat().st_mode), 0o700)
        self.assertEqual(stat.S_IMODE(self.config.item_root.stat().st_mode), 0o711)
        self.assertEqual(stat.S_IMODE(self.config.home_root.stat().st_mode), 0o711)
        self.assertEqual(
            stat.S_IMODE(self.config.controller_log_root.stat().st_mode), 0o700,
        )
        self.assertEqual(
            stat.S_IMODE((self.config.campaign_root / "quarantine").stat().st_mode),
            0o700,
        )

    def test_aggregate_index_is_atomic_and_contains_no_peer_payloads(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        self.config.campaign_root.mkdir()
        value = RUNNER._base_index(self.config, identities)
        value["source_lineage"] = {
            "parent_manifest_sha256": "0" * 64,
            "parent_bundle_sha256": "1" * 64,
            "canonical_row_sha256": {
                target_id: "2" * 64 for target_id in RUNNER.CANONICAL_TARGET_IDS
            },
        }
        value["controller"].update({
            "runtime_inventory_sha256": "3" * 64,
            "dependency_inventory_sha256": "4" * 64,
            "original_seed_manifest_sha256": "0" * 64,
            "original_seed_bundle_sha256": "1" * 64,
        })
        RUNNER._atomic_write(self.config.index_path, value)
        loaded = json.loads(self.config.index_path.read_text(encoding="utf-8"))
        RUNNER._validate_aggregate_index(self.config, loaded)
        self.assertNotIn("question", self.config.index_path.read_text(encoding="utf-8"))
        self.assertFalse(self.config.index_path.with_name(".campaign.json.tmp").exists())

    def test_deny_probe_inventory_has_every_peer_and_proc(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        selected = identities[0]
        paths = set(RUNNER._deny_probe_paths(self.config, selected, identities, [41, 42]))
        self.assertIn(Path("/proc/self/cmdline"), paths)
        self.assertIn(Path("/proc/41/cmdline"), paths)
        self.assertIn(self.config.campaign_root, paths)
        self.assertIn(self.config.target_root(identities[1].target_id), paths)
        self.assertIn(self.config.user_home(identities[1].target_id), paths)
        self.assertNotIn(self.config.target_root(selected.target_id), paths)

    def test_system_allowlist_uses_exact_files_and_no_tty(self) -> None:
        runtime = self.base / "runtime"
        runtime.mkdir()
        allowed_file = self.base / "ld.so"
        allowed_file.write_text("loader", encoding="utf-8")
        with (
            mock.patch.object(
                RUNNER.ITERATION,
                "_system_readonly_inventory",
                return_value=((allowed_file,), {str(allowed_file): "0" * 64}),
            ),
            mock.patch.object(
                RUNNER, "_system_read_write_paths",
                return_value=(Path("/dev/null"),),
            ),
        ):
            paths = RUNNER._system_read_paths(runtime)
        self.assertIn(allowed_file, paths)
        self.assertNotIn(Path("/dev/null"), paths)
        self.assertEqual(
            RUNNER._LANDLOCK_READ_WRITE_DEVICE_FILES,
            ("/dev/null",),
        )
        for raw in ("/dev/zero", "/dev/random", "/dev/urandom"):
            if Path(raw).exists():
                self.assertIn(Path(raw).resolve(strict=True), paths)
        self.assertNotIn(Path("/usr/lib"), paths)
        self.assertNotIn(Path("/lib"), paths)
        self.assertNotIn(Path("/usr/bin"), paths)
        self.assertNotIn(Path("/usr/bin/git"), paths)
        self.assertNotIn(Path("/dev/tty"), paths)

    def test_system_read_write_paths_requires_canonical_dev_null(self) -> None:
        canonical = mock.Mock(
            st_mode=stat.S_IFCHR | 0o666,
            st_rdev=os.makedev(1, 3),
            st_uid=0,
            st_gid=0,
        )
        unsafe = {
            "regular-file": mock.Mock(
                st_mode=stat.S_IFREG | 0o666,
                st_rdev=os.makedev(1, 3),
                st_uid=0,
                st_gid=0,
            ),
            "wrong-device": mock.Mock(
                st_mode=stat.S_IFCHR | 0o666,
                st_rdev=os.makedev(1, 5),
                st_uid=0,
                st_gid=0,
            ),
            "wrong-mode": mock.Mock(
                st_mode=stat.S_IFCHR | 0o644,
                st_rdev=os.makedev(1, 3),
                st_uid=0,
                st_gid=0,
            ),
            "wrong-uid": mock.Mock(
                st_mode=stat.S_IFCHR | 0o666,
                st_rdev=os.makedev(1, 3),
                st_uid=1,
                st_gid=0,
            ),
            "wrong-gid": mock.Mock(
                st_mode=stat.S_IFCHR | 0o666,
                st_rdev=os.makedev(1, 3),
                st_uid=0,
                st_gid=1,
            ),
        }
        with (
            mock.patch.object(Path, "resolve", return_value=Path("/dev/null")),
            mock.patch.object(Path, "stat", return_value=canonical),
        ):
            self.assertEqual(
                RUNNER._system_read_write_paths(),
                (Path("/dev/null"),),
            )
        for label, metadata in unsafe.items():
            with (
                self.subTest(label=label),
                mock.patch.object(Path, "resolve", return_value=Path("/dev/null")),
                mock.patch.object(Path, "stat", return_value=metadata),
                self.assertRaisesRegex(RUNNER.CampaignError, "unsafe"),
            ):
                RUNNER._system_read_write_paths()

    def test_codex_home_rejects_hardlinked_auth(self) -> None:
        template = self.config.codex_home_template
        template.mkdir(parents=True)
        template.chmod(0o700)
        auth = template / "auth.json"
        auth.write_text("{}\n", encoding="utf-8")
        auth.chmod(0o600)
        os.link(auth, template / "auth.peer")
        identity = RUNNER._identity_plan(self.config)[0]
        with self.assertRaisesRegex(RUNNER.CampaignError, "plain auth"):
            RUNNER._prepare_codex_home(self.config, identity)

    def test_subset_seed_derives_pdf_only_from_target_images(self) -> None:
        seed = self.config.seed_workspace
        seed.mkdir(parents=True)
        lake_rel = "lakefile.toml"
        (seed / lake_rel).write_text("name = \"x\"\n", encoding="utf-8")
        lake_sha = hashlib.sha256((seed / lake_rel).read_bytes()).hexdigest()
        image_names = ("only-a.png", "only-b.png")
        image_assets: dict[str, str] = {}
        for index, name in enumerate(image_names):
            path = seed / "icho_2026_source/image" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            Image.new("RGB", (20 + index, 30), (10, 20, 30)).save(path)
            image_assets[f"icho_2026_source/image/{name}"] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
        full_pdf = seed / "icho_2026_source/raw/theory_problem.pdf"
        full_pdf.parent.mkdir(parents=True)
        full_pdf.write_bytes(b"FULL-PAPER-ANSWER-BEARING-SURFACE")
        full_pdf_sha = hashlib.sha256(full_pdf.read_bytes()).hexdigest()
        manifest = {
            "schema_version": 1,
            "protocol": "icho-problem-only-solver-seed-v1",
            "source_revision_disclosed": False,
            "engine_files": {},
            "engine_files_sha256": RUNNER._hash_index({}),
            "lake_skeleton_files": {lake_rel: lake_sha},
            "lake_skeleton_sha256": RUNNER._hash_index({lake_rel: lake_sha}),
            "assets": {**image_assets, "icho_2026_source/raw/theory_problem.pdf": full_pdf_sha},
            "isolation_claims": {"filesystem": True, "network": False},
            "workspace_policy": {"fresh_git_init": True, "history": False, "remotes": [], "solver_labels": ["GPT", "K3"]},
        }
        target_id = RUNNER.CANONICAL_TARGET_IDS[0]
        row = {
            "schema_version": 1,
            "protocol": "icho-answer-blind-v1",
            "id": target_id,
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "source_pdf": "theory_problem.pdf",
            "images": list(image_names),
            "problem_assets": [
                *(
                    {"kind": "problem_page", "path": name, "sha256": image_assets[f"icho_2026_source/image/{name}"]}
                    for name in image_names
                ),
                {"kind": "problem_pdf", "path": "theory_problem.pdf", "sha256": full_pdf_sha},
            ],
        }
        destination = self.base / "subset"
        with mock.patch.object(RUNNER.NATIVE._SEED, "validate_seed") as validate:
            receipt = RUNNER._build_subset_seed(
                seed=seed, destination=destination, manifest=manifest, row=row,
            )
        validate.assert_called_once_with(destination)
        projected = json.loads((destination / RUNNER.BUNDLE_REL).read_text())
        self.assertNotEqual(projected["source_pdf"], "theory_problem.pdf")
        self.assertFalse((destination / "icho_2026_source/raw/theory_problem.pdf").exists())
        derived = destination / receipt["derived_pdf"]["path"]
        self.assertTrue(derived.read_bytes().startswith(b"%PDF"))
        self.assertNotIn(full_pdf.read_bytes(), derived.read_bytes())
        self.assertEqual(
            [item["sha256"] for item in receipt["derived_pdf"]["source_images"]],
            [image_assets[f"icho_2026_source/image/{name}"] for name in image_names],
        )
        self.assertEqual(json.loads((destination / RUNNER.MANIFEST_REL).read_text())["target_ids"], [target_id])

    def test_prepare_uses_bounded_four_workers(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        rows = {item.target_id: {"id": item.target_id} for item in identities}
        self.config.seed_workspace.mkdir()
        (self.config.seed_workspace / RUNNER.MANIFEST_REL).write_text("{}\n")
        bundle = self.config.seed_workspace / RUNNER.BUNDLE_REL
        bundle.parent.mkdir()
        bundle.write_text("{}\n")
        fake_executor = mock.MagicMock()
        fake_executor.__enter__.return_value = fake_executor
        fake_executor.__exit__.return_value = False
        with (
            mock.patch.object(RUNNER, "_validate_fresh_config", return_value=(self.base / "seed", self.base / "packages")),
            mock.patch.object(RUNNER, "_ensure_identities"),
            mock.patch.object(RUNNER, "_load_full_seed", return_value=({}, rows)),
            mock.patch.object(RUNNER, "_runtime_root", return_value=self.base / "runtime"),
            mock.patch.object(RUNNER, "_prepare_layout"),
            mock.patch.object(RUNNER, "_copy_dependency_snapshot"),
            mock.patch.object(RUNNER, "_controller_tree_digest", return_value="0" * 64),
            mock.patch.object(RUNNER, "_atomic_write"),
            mock.patch.object(RUNNER, "_acquire_campaign_lock", return_value=70),
            mock.patch.object(RUNNER, "_acquire_uid_locks", return_value=[]),
            mock.patch.object(
                RUNNER, "_cleanup_identity_processes",
                return_value={"quiescent_after": True},
            ),
            mock.patch.object(RUNNER, "_set_campaign_solver_access"),
            mock.patch.object(RUNNER, "ThreadPoolExecutor", return_value=fake_executor) as pool,
            mock.patch.object(RUNNER, "as_completed", return_value=[]),
            mock.patch.object(RUNNER, "_verify_dac_isolation"),
            mock.patch.object(RUNNER.os, "close"),
        ):
            RUNNER.prepare_campaign(self.config, start=False)
        pool.assert_called_once_with(max_workers=4, thread_name_prefix="isolated-prepare")
        self.assertEqual(fake_executor.submit.call_count, 32)

    def test_batch_receipts_do_not_let_one_pending_fd_block_ready_peer(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        ready_read, ready_write = os.pipe()
        pending_read, pending_write = os.pipe()
        ready = RUNNER._Child(identities[0], 101, -1, -1, ready_read, -1, 0.0)
        pending = RUNNER._Child(identities[1], 102, -1, -1, pending_read, -1, 0.0)
        RUNNER._write_child_receipt(ready_write, {"target_id": identities[0].target_id})
        os.close(ready_write)
        receipts, errors = RUNNER._read_batch_receipts(
            (ready, pending), timeout_seconds=0.05,
        )
        os.close(pending_write)
        self.assertEqual(receipts[101]["target_id"], identities[0].target_id)
        self.assertIn("timed out", errors[102])

    def test_cleanup_requires_full_quiet_window(self) -> None:
        identity = RUNNER._identity_plan(self.config)[0]
        clock = [0.0]
        scans = iter([(), (), (55,), (), (), (), ()])

        def pids(_uid: int):
            try:
                return next(scans)
            except StopIteration:
                return ()

        def monotonic() -> float:
            return clock[0]

        def sleep(seconds: float) -> None:
            clock[0] += max(seconds, 0.25)

        with (
            mock.patch.object(RUNNER, "_uid_pids", side_effect=pids),
            mock.patch.object(RUNNER.ITERATION, "_reap_controller_children"),
            mock.patch.object(RUNNER.time, "monotonic", side_effect=monotonic),
            mock.patch.object(RUNNER.time, "sleep", side_effect=sleep),
            mock.patch.object(RUNNER, "_proc_identity", side_effect=FileNotFoundError),
        ):
            receipt = RUNNER._cleanup_identity_processes(identity, quiet_period_ms=600)
        self.assertGreaterEqual(clock[0], 1.0)
        self.assertTrue(receipt["quiescent_after"])

    def test_cleanup_binds_pidfd_before_proc_identity_and_signals(self) -> None:
        identity = RUNNER._identity_plan(self.config)[0]
        scans = iter([(123,), (123,), (123,), (), (), (), ()])
        clock = [0.0]
        order: list[str] = []

        def pids(_uid: int):
            try:
                return next(scans)
            except StopIteration:
                return ()

        def pidfd_open(_pid: int, _flags: int) -> int:
            order.append("pidfd")
            return 88

        proc_calls = [0]

        def proc_identity(_pid: int):
            proc_calls[0] += 1
            order.append(f"proc{proc_calls[0]}")
            return identity.uid, "start", "S" if proc_calls[0] == 1 else "T"

        def send(_pidfd: int, signum: int) -> None:
            order.append(f"signal:{signum}")

        with (
            mock.patch.object(RUNNER, "_uid_pids", side_effect=pids),
            mock.patch.object(RUNNER.ITERATION, "_reap_controller_children"),
            mock.patch.object(RUNNER.os, "pidfd_open", side_effect=pidfd_open),
            mock.patch.object(RUNNER, "_proc_identity", side_effect=proc_identity),
            mock.patch.object(RUNNER.signal, "pidfd_send_signal", side_effect=send),
            mock.patch.object(
                RUNNER.resource, "prlimit", side_effect=lambda *_a: order.append("prlimit"),
            ),
            mock.patch.object(RUNNER.os, "close"),
            mock.patch.object(RUNNER.time, "monotonic", side_effect=lambda: clock[0]),
            mock.patch.object(
                RUNNER.time, "sleep",
                side_effect=lambda seconds: clock.__setitem__(0, clock[0] + max(seconds, 0.7)),
            ),
        ):
            receipt = RUNNER._cleanup_identity_processes(identity)
        self.assertTrue(receipt["quiescent_after"])
        self.assertLess(order.index("pidfd"), order.index("proc1"))
        self.assertLess(order.index("proc1"), order.index(f"signal:{RUNNER.signal.SIGSTOP}"))
        self.assertIn(f"signal:{RUNNER.signal.SIGKILL}", order)

    def test_cleanup_resumes_pidfd_bound_process_on_post_stop_mismatch(self) -> None:
        identity = RUNNER._identity_plan(self.config)[0]
        signals: list[int] = []
        with (
            mock.patch.object(RUNNER, "_uid_pids", return_value=(123,)),
            mock.patch.object(RUNNER.ITERATION, "_reap_controller_children"),
            mock.patch.object(RUNNER.os, "pidfd_open", return_value=88),
            mock.patch.object(
                RUNNER, "_proc_identity",
                side_effect=[
                    (identity.uid, "old", "S"),
                    (identity.uid, "reused", "T"),
                ],
            ),
            mock.patch.object(
                RUNNER.signal, "pidfd_send_signal",
                side_effect=lambda _fd, signum: signals.append(signum),
            ),
            mock.patch.object(RUNNER.os, "close"),
        ):
            with self.assertRaisesRegex(RUNNER.CampaignError, "identity changed"):
                RUNNER._cleanup_identity_processes(identity)
        self.assertEqual(signals, [RUNNER.signal.SIGSTOP, RUNNER.signal.SIGCONT])

    def test_identity_sweep_continues_after_one_uid_cleanup_failure(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        visited: list[str] = []

        def cleanup(identity):
            visited.append(identity.target_id)
            if identity == identities[4]:
                raise RUNNER.CampaignError("synthetic cleanup failure")
            return {"quiescent_after": True}

        with mock.patch.object(
            RUNNER, "_cleanup_identity_processes", side_effect=cleanup,
        ):
            receipts, errors = RUNNER._sweep_identities(
                identities, phase="startup UID sweep",
            )
        self.assertEqual(visited, list(RUNNER.CANONICAL_TARGET_IDS))
        self.assertEqual(len(receipts), 31)
        self.assertEqual(len(errors), 1)
        self.assertIn(identities[4].target_id, errors[0])

    def test_verified_run_preflight_error_still_sweeps_all_identities(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        library = mock.MagicMock()
        library.prctl.return_value = 0
        with (
            mock.patch.object(RUNNER, "_libc", return_value=library),
            mock.patch.object(RUNNER, "_identity_plan", return_value=identities),
            mock.patch.object(RUNNER, "_ensure_identities"),
            mock.patch.object(
                RUNNER, "_run_campaign_verified",
                side_effect=RUNNER.CampaignError("preflight failed"),
            ),
            mock.patch.object(
                RUNNER, "_sweep_identities", return_value=({}, []),
            ) as sweep,
        ):
            with self.assertRaisesRegex(RUNNER.CampaignError, "preflight failed"):
                RUNNER._run_campaign_locked(self.config, resume=True)
        sweep.assert_called_once_with(identities, phase="final UID sweep")

    def test_child_receipt_write_handles_partial_writes(self) -> None:
        chunks: list[bytes] = []

        def partial(_fd: int, payload: bytes) -> int:
            amount = min(3, len(payload))
            chunks.append(payload[:amount])
            return amount

        with mock.patch.object(RUNNER.os, "write", side_effect=partial):
            RUNNER._write_child_receipt(99, {"payload": "longer than pipe atom"})
        self.assertEqual(json.loads(b"".join(chunks)), {"payload": "longer than pipe atom"})

    def test_spawn_fails_closed_when_prepare_thread_is_alive(self) -> None:
        identity = RUNNER._identity_plan(self.config)[0]
        with mock.patch.object(RUNNER.threading, "active_count", return_value=2):
            with self.assertRaisesRegex(RUNNER.CampaignError, "single-thread"):
                RUNNER._spawn_child(self.config, identity, (identity,), resume=False)

    def test_no_root_combined_build_of_solver_authored_lean(self) -> None:
        source = SCRIPT.read_text(encoding="utf-8")
        self.assertNotIn("_run_root_only_combined_build", source)
        self.assertNotIn("combined-lake-build.log", source)
        self.assertIn("unsafe_root_execution_forbidden", source)

    def test_prepare_holds_uid_locks_and_seals_root_before_return(self) -> None:
        lock_fds = [71, 72]
        self.config.campaign_root.mkdir()
        with (
            mock.patch.object(RUNNER, "_acquire_campaign_lock", return_value=70),
            mock.patch.object(RUNNER, "_acquire_uid_locks", return_value=lock_fds),
            mock.patch.object(RUNNER, "_prepare_campaign_locked", return_value={"status": "prepared"}),
            mock.patch.object(RUNNER, "_identity_plan", return_value=()),
            mock.patch.object(RUNNER, "_verify_dac_isolation"),
            mock.patch.object(RUNNER, "_atomic_write"),
            mock.patch.object(RUNNER, "_set_campaign_solver_access") as access,
            mock.patch.object(RUNNER.os, "close") as close,
        ):
            result = RUNNER.prepare_campaign(self.config, start=False)
        self.assertEqual(result["status"], "prepared")
        self.assertEqual(
            [call.kwargs["enabled"] for call in access.call_args_list],
            [True, False],
        )
        self.assertEqual([call.args[0] for call in close.call_args_list], [72, 71, 70])

    def test_lock_failure_never_changes_campaign_access(self) -> None:
        with (
            mock.patch.object(
                RUNNER, "_acquire_campaign_lock",
                side_effect=RUNNER.CampaignError("busy"),
            ),
            mock.patch.object(RUNNER, "_acquire_uid_locks") as uid_locks,
            mock.patch.object(RUNNER, "_set_campaign_solver_access") as access,
        ):
            with self.assertRaisesRegex(RUNNER.CampaignError, "busy"):
                RUNNER.prepare_campaign(self.config, start=False)
        uid_locks.assert_not_called()
        access.assert_not_called()

    def test_resume_sweeps_uids_before_reading_solver_owned_state(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        index = {
            "targets": {
                target_id: {"status": "pending"}
                for target_id in RUNNER.CANONICAL_TARGET_IDS
            }
        }
        order: list[str] = []

        def sweep(_identities, *, phase: str):
            order.append(phase)
            return {}, []

        with (
            mock.patch.object(RUNNER, "_acquire_campaign_lock", return_value=70),
            mock.patch.object(RUNNER, "_stored_config", return_value=self.config),
            mock.patch.object(RUNNER, "_acquire_uid_locks", return_value=[]),
            mock.patch.object(RUNNER, "_load_index", return_value=index),
            mock.patch.object(RUNNER, "_identity_plan", return_value=identities),
            mock.patch.object(
                RUNNER, "_ensure_identities", side_effect=lambda *_a: order.append("identity"),
            ),
            mock.patch.object(RUNNER, "_sweep_identities", side_effect=sweep),
            mock.patch.object(
                RUNNER, "_verify_resume_bindings",
                side_effect=lambda *_a: order.append("bindings"),
            ),
            mock.patch.object(
                RUNNER, "_finish_partial_preparation",
                side_effect=lambda *_a: order.append("partial") or index,
            ),
            mock.patch.object(RUNNER, "_set_campaign_solver_access"),
            mock.patch.object(
                RUNNER, "_run_campaign_locked",
                return_value={"status": "succeeded"},
            ),
            mock.patch.object(RUNNER.os, "close"),
        ):
            result = RUNNER.resume_campaign(self.config.campaign_root)
        self.assertEqual(result["status"], "succeeded")
        self.assertLess(order.index("resume preflight UID sweep"), order.index("bindings"))
        self.assertLess(order.index("bindings"), order.index("partial"))
        self.assertEqual(order[-1], "resume final UID sweep")

    def test_partial_prepare_quarantines_target_and_home_together(self) -> None:
        identity = RUNNER._identity_plan(self.config)[0]
        target = self.config.target_root(identity.target_id)
        home = self.config.user_home(identity.target_id)
        target.mkdir(parents=True)
        home.mkdir(parents=True)
        (target / "old").write_text("target", encoding="utf-8")
        (home / "old").write_text("home", encoding="utf-8")
        (self.config.campaign_root / "quarantine").mkdir()
        projection = {
            "parent_row_sha256": "1" * 64,
            "projected_row_sha256": "2" * 64,
            "derived_pdf": {},
        }
        with (
            mock.patch.object(RUNNER, "_build_subset_seed", return_value=projection),
            mock.patch.object(
                RUNNER.NATIVE, "run_fresh",
                return_value={"status": "prepared", "native": {}, "grounding": {}},
            ),
            mock.patch.object(RUNNER, "_prepare_codex_home", return_value="3" * 64),
            mock.patch.object(RUNNER, "_harden_target"),
        ):
            RUNNER._prepare_one(
                self.config, identity, full_manifest={}, row={"id": identity.target_id},
            )
        quarantines = list((self.config.campaign_root / "quarantine").iterdir())
        self.assertEqual(len(quarantines), 1)
        self.assertEqual((quarantines[0] / "target/old").read_text(), "target")
        self.assertEqual((quarantines[0] / "home/old").read_text(), "home")

    def test_receipt_validation_requires_all_peer_and_proc_probes(self) -> None:
        identities = RUNNER._identity_plan(self.config)
        identity = identities[0]
        paths = list(RUNNER._deny_probe_paths(
            self.config, identity, identities, (),
        ))
        paths.extend(
            self.config.codex_home(peer.target_id) / "auth.json"
            for peer in identities if peer != identity
        )
        receipt = {
            "target_id": identity.target_id,
            "uid": identity.uid,
            "gid": identity.gid,
            "filesystem_answer_blind": True,
            "network_answer_blind": False,
            "landlock": {"abi": 4, "deny_by_default": True, "no_new_privs": True},
            "isolation_probes": [
                {"path": str(path), "denied": True, "errno": 13}
                for path in paths
            ],
        }
        RUNNER._validate_isolation_receipt(
            self.config, identity, identities, receipt,
        )
        receipt["isolation_probes"] = [
            row for row in receipt["isolation_probes"]
            if row["path"] != "/proc/self/cmdline"
        ]
        with self.assertRaisesRegex(RUNNER.CampaignError, "omits peer/proc"):
            RUNNER._validate_isolation_receipt(
                self.config, identity, identities, receipt,
            )


@unittest.skipUnless(os.geteuid() == 0, "real Landlock probe is root-only")
class RealLandlockIsolationTests(unittest.TestCase):
    def test_real_kernel_denies_proc_and_peer_but_allows_own(self) -> None:
        if RUNNER.landlock_abi() < 4:
            self.skipTest("Landlock ABI 4 required")
        with tempfile.TemporaryDirectory(prefix="isolated-landlock-") as raw:
            root = Path(raw)
            own = root / "own"
            peer = root / "peer"
            own.mkdir()
            peer.mkdir()
            (own / "value").write_text("own", encoding="utf-8")
            (peer / "value").write_text("peer", encoding="utf-8")
            pid = os.fork()
            if pid == 0:
                try:
                    RUNNER._apply_landlock(read_only=(own,), read_write=())
                    self_value = (own / "value").read_text()
                    try:
                        (peer / "value").read_text()
                    except PermissionError:
                        peer_denied = True
                    else:
                        peer_denied = False
                    try:
                        Path("/proc/self/cmdline").read_bytes()
                    except PermissionError:
                        proc_denied = True
                    else:
                        proc_denied = False
                    os._exit(0 if self_value == "own" and peer_denied and proc_denied else 1)
                except BaseException:
                    os._exit(2)
            _waited, status = os.waitpid(pid, 0)
            self.assertEqual(os.waitstatus_to_exitcode(status), 0)

    def test_real_kernel_allows_sealed_git_and_dev_null_but_denies_system_git(self) -> None:
        if RUNNER.landlock_abi() < 4:
            self.skipTest("Landlock ABI 4 required")
        source_git_raw = shutil.which("git")
        if source_git_raw is None:
            self.skipTest("git is required for the real Landlock regression")
        source_git = Path(source_git_raw).resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix="isolated-landlock-git-") as raw:
            root = Path(raw)
            runtime = root / "runtime"
            runtime_git = runtime / "bin/git"
            checkout = root / "crnt"
            peer = root / "peer"
            runtime_git.parent.mkdir(parents=True)
            checkout.mkdir()
            peer.mkdir()
            shutil.copy2(source_git, runtime_git)
            subprocess.run(
                [str(runtime_git), "init", "--quiet", "--initial-branch=main", "--template="],
                cwd=checkout, check=True,
            )
            (checkout / "CRNT.lean").write_text("def crnt := 1\n", encoding="utf-8")
            subprocess.run([str(runtime_git), "add", "CRNT.lean"], cwd=checkout, check=True)
            subprocess.run(
                [
                    str(runtime_git), "-c", "user.name=Test", "-c",
                    "user.email=test@example.invalid", "commit", "--quiet", "-m", "init",
                ],
                cwd=checkout, check=True,
            )
            remote_url = "https://example.invalid/crnt-lean"
            subprocess.run(
                [str(runtime_git), "remote", "add", "origin", remote_url],
                cwd=checkout, check=True,
            )
            revision = subprocess.check_output(
                [str(runtime_git), "rev-parse", "HEAD"], cwd=checkout, text=True,
            ).strip()
            (peer / "value").write_text("peer", encoding="utf-8")
            try:
                read_write = RUNNER._system_read_write_paths()
            except RUNNER.CampaignError as exc:
                self.skipTest(f"host has no safe writable /dev/null: {exc}")
            read_only = (
                runtime, checkout, *RUNNER._system_read_paths(runtime),
            )

            for path in sorted(root.rglob("*"), key=lambda item: len(item.parts), reverse=True):
                if path.is_symlink():
                    continue
                os.chown(path, 0, 0)
                if path.is_dir():
                    os.chmod(path, 0o555)
                elif path == runtime_git:
                    os.chmod(path, 0o555)
                else:
                    os.chmod(path, 0o444)
            os.chown(root, 0, 0)
            os.chmod(root, 0o755)

            read_fd, write_fd = os.pipe()
            pid = os.fork()
            if pid == 0:
                os.close(read_fd)
                try:
                    receipt = RUNNER._apply_landlock(
                        read_only=read_only, read_write=read_write,
                    )
                    os.setgroups([])
                    os.setgid(65534)
                    os.setuid(65534)
                    os.environ.clear()
                    os.environ.update({
                        "PATH": str(runtime_git.parent),
                        "HOME": str(root / "absent-home"),
                        "LANG": "C.UTF-8",
                        "LC_ALL": "C.UTF-8",
                        "GIT_CONFIG_NOSYSTEM": "1",
                        "GIT_CONFIG_GLOBAL": os.devnull,
                    })
                    actual_revision = RUNNER.NATIVE._crnt_git_value(
                        checkout, "rev-parse", "HEAD",
                    )
                    actual_url = RUNNER.NATIVE._crnt_git_value(
                        checkout, "remote", "get-url", "origin",
                    )
                    descriptor = os.open(
                        os.devnull, os.O_RDWR | os.O_CLOEXEC,
                    )
                    try:
                        os.write(descriptor, b"landlock-regression\n")
                    finally:
                        os.close(descriptor)
                    denied = all(
                        RUNNER._negative_open_probe(path)["denied"]
                        for path in (
                            peer / "value", Path("/proc/self/cmdline"),
                            Path("/usr/bin/git"), Path("/usr/bin"), Path("/usr/lib"),
                        )
                    )
                    authorized = set(receipt["read_only_paths"]) | set(
                        receipt["read_write_paths"]
                    )
                    exact_surface = all(
                        str(path) not in authorized
                        for path in (Path("/usr/bin/git"), Path("/usr/bin"), Path("/usr/lib"))
                    )
                    ok = (
                        actual_revision == revision
                        and actual_url == remote_url
                        and denied
                        and exact_surface
                        and receipt["read_write_paths"] == [str(Path(os.devnull))]
                    )
                    os.write(write_fd, ("ok\n" if ok else "assertion failed\n").encode())
                    os._exit(0 if ok else 1)
                except BaseException as exc:
                    os.write(write_fd, f"{type(exc).__name__}: {exc}\n".encode())
                    os._exit(2)
            os.close(write_fd)
            message = os.read(read_fd, 4096).decode("utf-8", errors="replace").strip()
            os.close(read_fd)
            _waited, status = os.waitpid(pid, 0)
            self.assertEqual(os.waitstatus_to_exitcode(status), 0, message)


if __name__ == "__main__":
    unittest.main()
