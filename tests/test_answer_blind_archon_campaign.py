from __future__ import annotations

import importlib.util
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_answer_blind_archon_campaign.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_archon_campaign", SCRIPT)
assert SPEC and SPEC.loader
RUNNER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = RUNNER
SPEC.loader.exec_module(RUNNER)


class NativeArchonCampaignTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="native-archon-campaign-")
        self.base = Path(self.temporary.name)
        self.seed = self.base / "seed"
        self.seed.mkdir()
        self.ids = tuple(f"icho_2026_t{index:02d}_a1" for index in range(1, 33))
        (self.seed / "isolation_manifest.json").write_text(
            json.dumps({"target_ids": list(self.ids)}), encoding="utf-8"
        )
        source = self.seed / "icho_2026_source"
        (source / "image").mkdir(parents=True)
        (source / "questions_only.jsonl").write_text(
            "".join(
                json.dumps({
                    "id": record_id,
                    "evaluation_mode": "answer_blind",
                    "official_answer_seen": False,
                    "question": f"Question {record_id}",
                }) + "\n"
                for record_id in self.ids
            ),
            encoding="utf-8",
        )
        (self.seed / "IChO2026Problems.lean").write_text(
            "import IChO2026Problems.All\n", encoding="utf-8"
        )
        self.packages = self.base / "packages"
        self.packages.mkdir()
        self.config = RUNNER.Config(
            campaign_root=self.base / "campaign",
            seed_workspace=self.seed,
            lake_packages=self.packages,
            archon_bin="/runtime/bin/archon",
            max_iterations=17,
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def _fake_copy(seed: Path, destination: Path, *, label: str) -> None:
        del label
        shutil.copytree(seed, destination)

    @staticmethod
    def _fake_configure(workspace: Path, **_kwargs: object) -> dict[str, object]:
        state = workspace / ".archon"
        state.mkdir()
        (state / "config.json").write_text(
            json.dumps({
                "loop": {
                    "max_parallel": 32,
                    "review_preflight_jobs": 32,
                    "parallel_target_review_jobs": 32,
                    "parallel_formalization_review_jobs": 32,
                    "parallel_target_review": True,
                    "parallel_formalization_review": True,
                    "pipeline_target_review": True,
                    "domain_profile": {"name": "chemistry"},
                },
                "harnesses": {
                    "answer-blind-gpt": {
                        "runner": "codex",
                        "base_url_env": "OLD_BASE",
                        "key_env": "OLD_KEY",
                        "wire_api": "responses",
                        "sandbox": "workspace-write",
                        "extra_args": ["-c", "web_search=\"disabled\""],
                    }
                },
            }),
            encoding="utf-8",
        )
        return {}

    def _prepare_patches(self):
        return (
            mock.patch.object(RUNNER._SEED, "validate_seed", return_value={}),
            mock.patch.object(
                RUNNER._SEED, "copy_seed_to_workspace", side_effect=self._fake_copy
            ),
            mock.patch.object(
                RUNNER._CONFIGURE,
                "configure_answer_blind_workspace",
                side_effect=self._fake_configure,
            ),
        )

    def _write_physics_metadata(self, workspace: Path) -> None:
        path = workspace / ".archon/physics-formalize/latest.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        work_dir = workspace / ".archon/physics-formalize/full32"
        work_dir.mkdir(parents=True, exist_ok=True)
        records = [
            {"rel_lean": target}
            for target in RUNNER._targets(self.ids)
        ]
        (work_dir / "summary.jsonl").write_text(
            "".join(json.dumps(record) + "\n" for record in records),
            encoding="utf-8",
        )
        path.write_text(json.dumps({
            "command": "physics-formalize",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "work_dir": str(work_dir),
            "entries": [{"id": record_id} for record_id in self.ids],
        }), encoding="utf-8")
        chapters = workspace / "blueprint/src/chapters"
        chapters.mkdir(parents=True, exist_ok=True)
        for record_id in self.ids:
            (chapters / f"IChO2026Problems_problem_{record_id}.tex").write_text(
                "% archon:physics\n"
                "% archon:chemistry\n"
                f"% archon:source-report reports/icho_2026/problem_{record_id}.source.json\n"
                f"Problem-only chapter for {record_id}.\n",
                encoding="utf-8",
            )

    def _write_success_state(self, workspace: Path) -> None:
        state = workspace / ".archon"
        targets = RUNNER._targets(self.ids)
        (state / "formalization-review-gate.json").write_text(
            json.dumps({"targets": {target: {"status": "passed"} for target in targets}}),
            encoding="utf-8",
        )
        (state / "proof-review-gate.json").write_text(
            json.dumps({"targets": {target: {"status": "solved"} for target in targets}}),
            encoding="utf-8",
        )
        meta = state / "logs/iter-001/meta.json"
        meta.parent.mkdir(parents=True)
        meta.write_text(json.dumps({
            "completedAt": "2026-01-01T00:00:00Z",
            "sorry_count": 0,
            "finalize": {"lake": {"ok": True}},
        }), encoding="utf-8")

    def test_commands_are_one_native_full32_pipeline(self) -> None:
        physics = RUNNER.physics_command(self.config)
        first_loop = RUNNER.loop_command(self.config, resume=False)
        resumed = RUNNER.loop_command(self.config, resume=True)

        self.assertEqual(physics[:2], ["/runtime/bin/archon", "physics-formalize"])
        self.assertIn("answer-blind", physics)
        self.assertIn("-1", physics)
        self.assertEqual(first_loop[:2], ["/runtime/bin/archon", "loop"])
        self.assertIn("--from", first_loop)
        self.assertIn("prover", first_loop)
        self.assertIn("--max-parallel", first_loop)
        self.assertEqual(first_loop[first_loop.index("--max-parallel") + 1], "4")
        self.assertIn("--formalization-review-gate", first_loop)
        self.assertIn("--proof-review-gate", first_loop)
        self.assertNotIn("--no-finalize", first_loop)
        self.assertNotIn("--no-lake-build", first_loop)
        self.assertIn("--no-blueprint-web", first_loop)
        self.assertIn("--resume", resumed)
        self.assertNotIn("--from", resumed)

        source = SCRIPT.read_text(encoding="utf-8")
        self.assertNotIn("ThreadPoolExecutor", source)
        self.assertNotIn("run_answer_blind_structured_solver", source)
        self.assertNotIn("artifact-finalize", source)
        self.assertNotIn("blind-freeze", source.lower())
        self.assertNotIn("create_blind_controller_seal", source)

    def test_run_scopes_git_safe_directory_to_private_packages(self) -> None:
        config = RUNNER.Config(campaign_root=self.base / "campaign")
        config.campaign_root.mkdir()
        config.workspace.mkdir()
        with mock.patch.object(RUNNER.subprocess, "run") as run:
            run.return_value.returncode = 0
            code, _seconds = RUNNER._run(["archon", "--help"], config=config)

        self.assertEqual(code, 0)
        environment = run.call_args.kwargs["env"]
        self.assertEqual(environment["GIT_CONFIG_COUNT"], "2")
        self.assertEqual(environment["GIT_CONFIG_KEY_0"], "safe.directory")
        self.assertEqual(environment["GIT_CONFIG_VALUE_0"], str(config.workspace))
        self.assertEqual(environment["GIT_CONFIG_KEY_1"], "safe.directory")
        self.assertEqual(
            environment["GIT_CONFIG_VALUE_1"],
            str(config.private_lake_packages / "*"),
        )

    def test_prepare_uses_shared_helpers_and_patches_native_codex(self) -> None:
        with self._prepare_patches()[0] as validate, self._prepare_patches()[1] as copy, self._prepare_patches()[2] as configure:
            config, ids = RUNNER._fresh_config(self.config)
            RUNNER.prepare_workspace(config, ids)

        validate.assert_called_once_with(self.seed.resolve())
        copy.assert_called_once()
        configure.assert_called_once()
        workspace = config.workspace
        value = json.loads((workspace / ".archon/config.json").read_text())
        harness = value["harnesses"]["answer-blind-gpt"]
        loop = value["loop"]
        self.assertEqual(harness["runner"], "codex")
        self.assertEqual(harness["sandbox"], "workspace-write")
        self.assertEqual(harness["mcp"], [])
        self.assertNotIn("lean_lsp_mcp_bin", harness)
        self.assertIn("features.code_mode_host=false", harness["extra_args"])
        self.assertIn("features.shell_tool=true", harness["extra_args"])
        self.assertEqual(loop["domain_profile"]["name"], "chemistry")
        self.assertIs(loop["parallel_formalization_review"], False)
        self.assertIs(loop["parallel_target_review"], False)
        self.assertIs(loop["pipeline_target_review"], False)
        self.assertNotIn("base_url_env", harness)
        self.assertNotIn("key_env", harness)
        for key in (
            "max_parallel",
            "review_preflight_jobs",
            "parallel_target_review_jobs",
            "parallel_formalization_review_jobs",
        ):
            self.assertEqual(loop[key], 4)
        self.assertTrue((workspace / ".lake/packages").is_symlink())
        self.assertEqual(
            (workspace / ".lake/packages").resolve(),
            config.private_lake_packages,
        )
        self.assertTrue(config.private_lake_packages.is_dir())
        imports = (workspace / "IChO2026Problems/All.lean").read_text().splitlines()
        self.assertEqual(len(imports), 32)
        self.assertEqual(imports[0], f"import IChO2026Problems.problem_{self.ids[0]}")
        self.assertFalse((config.campaign_root / "workspaces").exists())
        agents = (workspace / ".archon/AGENTS.md").read_text()
        protocol = (workspace / "ANSWER_BLIND_PROTOCOL.md").read_text()
        formalize = (workspace / ".archon/prover-modes/physics-formalize.md").read_text()
        plan = (workspace / ".archon/prompts/plan.md").read_text()
        review = (workspace / ".archon/prompts/review.md").read_text()
        for text in (agents, protocol, formalize, plan, review):
            self.assertNotIn("freeze gates", text.lower())
            self.assertNotIn("lean-lsp mcp", text.lower())
        self.assertIn("formalization Review", agents)
        self.assertIn("create a candidate JSON", formalize)
        self.assertEqual(
            json.loads((workspace / ".mcp.json").read_text()),
            {"mcpServers": {}},
        )

    def test_default_fresh_run_prepares_without_starting_loop(self) -> None:
        commands: list[list[str]] = []

        def fake_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            commands.append(command)
            self._write_physics_metadata(config.workspace)
            return 0, 0.25

        patches = self._prepare_patches()
        with patches[0], patches[1], patches[2], mock.patch.object(
            RUNNER, "_run", side_effect=fake_run
        ):
            result = RUNNER.run_fresh(self.config, start_loop=False)

        self.assertEqual(result["status"], "prepared")
        self.assertEqual(len(commands), 1)
        self.assertEqual(commands[0][1], "physics-formalize")
        index = json.loads((self.config.campaign_root / "campaign.json").read_text())
        self.assertEqual(index["row_count"], 32)
        self.assertEqual(index["max_parallel"], 4)
        final_config = json.loads(
            (self.config.campaign_root / "workspace/.archon/config.json").read_text()
        )
        self.assertEqual(
            final_config["loop"]["domain_profile"]["name"], "chemistry-native"
        )
        chapters = self.config.campaign_root / "workspace/blueprint/src/chapters"
        for chapter in chapters.glob("*.tex"):
            self.assertNotIn("archon:source-report", chapter.read_text())
            self.assertNotIn("archon:physics", chapter.read_text())
            self.assertNotIn("archon:chemistry", chapter.read_text())

    def test_explicit_run_invokes_one_loop_and_uses_native_success(self) -> None:
        commands: list[list[str]] = []

        def fake_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            commands.append(command)
            if command[1] == "physics-formalize":
                self._write_physics_metadata(config.workspace)
            else:
                self._write_success_state(config.workspace)
            return 0, 0.5

        patches = self._prepare_patches()
        with patches[0], patches[1], patches[2], mock.patch.object(
            RUNNER, "_run", side_effect=fake_run
        ):
            result = RUNNER.run_fresh(self.config, start_loop=True)

        self.assertEqual([command[1] for command in commands], ["physics-formalize", "loop"])
        self.assertEqual(result["status"], "succeeded")
        self.assertTrue(result["native"]["complete"])
        self.assertEqual(result["native"]["formalization_review"], {"passed": 32})
        self.assertEqual(result["native"]["proof_review"], {"solved": 32})
        self.assertTrue(result["native"]["lake_build_ok"])
        self.assertEqual(result["native"]["sorry_count"], 0)

    def test_native_success_requires_final_lake_build(self) -> None:
        workspace = self.base / "native-state"
        (workspace / ".archon").mkdir(parents=True)
        self._write_success_state(workspace)
        meta = workspace / ".archon/logs/iter-001/meta.json"
        value = json.loads(meta.read_text())
        value["finalize"]["lake"]["ok"] = False
        meta.write_text(json.dumps(value), encoding="utf-8")

        result = RUNNER.native_summary(workspace, self.ids)

        self.assertFalse(result["complete"])
        self.assertFalse(result["lake_build_ok"])

    def test_nonzero_loop_cannot_reuse_an_old_complete_summary(self) -> None:
        config = RUNNER.Config(campaign_root=self.base / "failed-campaign")
        config.campaign_root.mkdir()
        config.workspace.mkdir()
        (config.workspace / ".archon").mkdir()
        self._write_success_state(config.workspace)
        index = {"pipeline": RUNNER.PIPELINE, "status": "running"}
        with mock.patch.object(RUNNER, "_run", return_value=(1, 0.1)):
            result = RUNNER._run_loop(config, self.ids, index, resume=False)
        self.assertEqual(result["status"], "failed")

    def test_prepared_campaign_starts_without_repreparing(self) -> None:
        patches = self._prepare_patches()

        def prepare_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            self._write_physics_metadata(config.workspace)
            return 0, 0.1

        with patches[0], patches[1], patches[2], mock.patch.object(
            RUNNER, "_run", side_effect=prepare_run
        ):
            RUNNER.run_fresh(self.config, start_loop=False)

        resume_config = RUNNER.Config(
            campaign_root=self.config.campaign_root,
            archon_bin=self.config.archon_bin,
            max_iterations=self.config.max_iterations,
        )
        seen: list[list[str]] = []

        def resume_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            seen.append(command)
            self._write_success_state(config.workspace)
            return 0, 0.2

        with (
            mock.patch.object(RUNNER._SEED, "copy_seed_to_workspace") as copy,
            mock.patch.object(
                RUNNER._CONFIGURE, "configure_answer_blind_workspace"
            ) as configure,
            mock.patch.object(RUNNER, "_run", side_effect=resume_run),
        ):
            result = RUNNER.resume_campaign(resume_config)

        copy.assert_not_called()
        configure.assert_not_called()
        self.assertEqual(len(seen), 1)
        self.assertIn("--from", seen[0])
        self.assertNotIn("--resume", seen[0])
        self.assertEqual(result["status"], "succeeded")

    def test_started_campaign_delegates_recovery_to_archon_resume(self) -> None:
        patches = self._prepare_patches()

        def prepare_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            self._write_physics_metadata(config.workspace)
            return 0, 0.1

        with patches[0], patches[1], patches[2], mock.patch.object(
            RUNNER, "_run", side_effect=prepare_run
        ):
            RUNNER.run_fresh(self.config, start_loop=False)

        index = self.config.campaign_root / "campaign.json"
        payload = json.loads(index.read_text())
        payload["status"] = "incomplete"
        index.write_text(json.dumps(payload), encoding="utf-8")
        resume_config = RUNNER.Config(
            campaign_root=self.config.campaign_root,
            archon_bin=self.config.archon_bin,
            max_iterations=self.config.max_iterations,
        )
        seen: list[list[str]] = []

        def resume_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            seen.append(command)
            self._write_success_state(config.workspace)
            return 0, 0.2

        with mock.patch.object(RUNNER, "_run", side_effect=resume_run):
            result = RUNNER.resume_campaign(resume_config)

        self.assertIn("--resume", seen[0])
        self.assertNotIn("--from", seen[0])
        self.assertEqual(result["status"], "succeeded")


if __name__ == "__main__":
    unittest.main()
