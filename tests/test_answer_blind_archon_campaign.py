from __future__ import annotations

import dataclasses
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
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
        crnt = self.packages / "crnt-lean"
        (crnt / "CRNT/Basic").mkdir(parents=True)
        (crnt / "CRNT.lean").write_text(
            "import CRNT.Basic.Reaction\n", encoding="utf-8"
        )
        (crnt / "CRNT/Basic/Reaction.lean").write_text(
            "namespace CRNT\n"
            "def indexedReactionBridge : Nat := 1\n"
            "end CRNT\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "init", "--quiet", "--initial-branch=main", "--template="],
            cwd=crnt,
            check=True,
        )
        subprocess.run(["git", "add", "."], cwd=crnt, check=True)
        subprocess.run(
            [
                "git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                "commit", "--quiet", "-m", "test CRNT pin",
            ],
            cwd=crnt,
            check=True,
        )
        crnt_url = "https://github.com/marpaia/crnt-lean"
        subprocess.run(
            ["git", "remote", "add", "origin", crnt_url], cwd=crnt, check=True
        )
        crnt_revision = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=crnt,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        self.crnt_url = crnt_url
        self.crnt_revision = crnt_revision
        (self.seed / "lake-manifest.json").write_text(
            json.dumps({
                "version": "1.2.0",
                "packages": [{
                    "name": "crnt-lean",
                    "type": "git",
                    "url": crnt_url,
                    "rev": crnt_revision,
                    "inputRev": crnt_revision,
                }],
            }),
            encoding="utf-8",
        )
        self.grounding_calls: list[dict[str, object]] = []
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
                "answer_blind": {
                    "authority": "problem-only",
                    "official_answer_seen": False,
                    "phase": "solve",
                    "protocol": "icho-answer-blind-v1",
                    "isolation": {
                        "filesystem_answer_blind": True,
                        "network_answer_blind": False,
                    },
                },
                "loop": {
                    "max_parallel": 32,
                    "review_preflight_jobs": 32,
                    "parallel_target_review_jobs": 32,
                    "parallel_formalization_review_jobs": 32,
                    "parallel_target_review": True,
                    "parallel_formalization_review": True,
                    "pipeline_target_review": True,
                    "domain_profile": {"name": "chemistry"},
                    "shared_infrastructure": {"enabled": False},
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

    def _fake_grounding(self, project: Path, **kwargs: object):
        self.grounding_calls.append(dict(kwargs))
        task_results = project / ".archon/task_results"
        task_results.mkdir(parents=True, exist_ok=True)
        reports = []
        for lean_file in kwargs.get("lean_files", []):
            lean_path = Path(lean_file)
            report_path = task_results / RUNNER.grounding_report_name(
                project, lean_path
            )
            report_path.write_text(
                "# Physics LeanExplore Grounding Log\n\n"
                "- Grounding status: complete\n"
                "- Search backend: hosted\n"
                f"- Input fingerprint: sha256:{'a' * 64}\n"
                "- Packages searched: Mathlib, Physlib, CRNT\n",
                encoding="utf-8",
            )
            reports.append(SimpleNamespace(
                lean_file=lean_path,
                report_path=report_path,
                is_complete=True,
            ))
        return reports

    def _grounding_patch(self):
        return mock.patch.object(
            RUNNER, "run_physics_grounding", side_effect=self._fake_grounding
        )

    def _prepare_only(self, config: RUNNER.Config | None = None) -> RUNNER.Config:
        selected = config or self.config

        def prepare_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            self._write_physics_metadata(config.workspace)
            return 0, 0.1

        patches = self._prepare_patches()
        with (
            patches[0], patches[1], patches[2], self._grounding_patch(),
            mock.patch.object(RUNNER, "_run", side_effect=prepare_run),
        ):
            result = RUNNER.run_fresh(selected, start_loop=False)
        self.assertEqual(result["status"], "prepared")
        return selected

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
        (state / "PROGRESS.md").write_text(
            "# Progress\n\n## Current Stage\n\nprover\n\n"
            "## Current Objectives\n\n",
            encoding="utf-8",
        )
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

    def test_explicit_nine_target_scope_is_prepared_and_bound(self) -> None:
        original_ids = self.ids
        subset = original_ids[:9]
        try:
            self.ids = subset
            (self.seed / "isolation_manifest.json").write_text(
                json.dumps({"target_ids": list(subset)}), encoding="utf-8"
            )
            bundle = self.seed / "icho_2026_source/questions_only.jsonl"
            bundle.write_text(
                "".join(
                    json.dumps({
                        "id": record_id,
                        "evaluation_mode": "answer-blind",
                        "official_answer_seen": False,
                        "question": f"Question {record_id}",
                    }) + "\n"
                    for record_id in subset
                ),
                encoding="utf-8",
            )
            config = dataclasses.replace(
                self.config,
                campaign_root=self.base / "campaign-nine",
                expected_items=9,
                max_parallel=9,
            )
            self._prepare_only(config)

            index = json.loads(config.index_path.read_text(encoding="utf-8"))
            self.assertEqual(index["row_count"], 9)
            native = json.loads(
                (config.workspace / ".archon/config.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(native["loop"]["max_objectives"], 9)
            self.assertEqual(native["loop"]["max_parallel"], 9)
            imports = (
                config.workspace / "IChO2026Problems/All.lean"
            ).read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(imports), 9)
            loop = RUNNER.loop_command(config, resume=False)
            self.assertEqual(loop[loop.index("--max-objectives") + 1], "9")
            parsed = RUNNER._parser().parse_args([
                "--campaign-root", str(self.base / "cli-nine"),
                "--expected-items", "9",
                "--max-parallel", "9",
                "--dry-run",
            ])
            self.assertEqual(parsed.expected_items, 9)
            self._write_success_state(config.workspace)
            self.assertTrue(RUNNER.native_summary(
                config.workspace, subset
            )["complete"])


            with self.assertRaisesRegex(
                RUNNER.CampaignError, "exactly 8 unique target_ids"
            ):
                RUNNER._target_ids(self.seed, expected_items=8)
        finally:
            self.ids = original_ids

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
        self.assertEqual(
            first_loop[first_loop.index("--max-iterations") + 1], "17"
        )
        self.assertEqual(
            first_loop[
                first_loop.index("--formalization-review-max-iterations") + 1
            ],
            "10",
        )
        self.assertEqual(
            first_loop[first_loop.index("--proof-review-max-iterations") + 1],
            "10",
        )
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
        for name in ("zeta", "alpha"):
            (config.private_lake_packages / name / ".git").mkdir(parents=True)
        (config.private_lake_packages / "not-a-git-package").mkdir()
        with mock.patch.object(RUNNER.subprocess, "run") as run:
            run.return_value.returncode = 0
            code, _seconds = RUNNER._run(["archon", "--help"], config=config)

        self.assertEqual(code, 0)
        environment = run.call_args.kwargs["env"]
        self.assertEqual(
            Path(environment["PATH"].split(RUNNER.os.pathsep)[0]),
            Path(shutil.which("archon")).resolve().parent,
        )
        self.assertEqual(environment["GIT_CONFIG_COUNT"], "3")
        self.assertEqual(
            [environment[f"GIT_CONFIG_KEY_{index}"] for index in range(3)],
            ["safe.directory"] * 3,
        )
        self.assertEqual(
            [environment[f"GIT_CONFIG_VALUE_{index}"] for index in range(3)],
            [
                str(config.workspace),
                str(config.private_lake_packages / "alpha"),
                str(config.private_lake_packages / "zeta"),
            ],
        )
        self.assertFalse(
            any(
                "*" in environment[f"GIT_CONFIG_VALUE_{index}"]
                for index in range(3)
            )
        )

    def test_loop_pins_exact_archon_and_smoke_checks_constant_service(self) -> None:
        config = RUNNER.Config(
            campaign_root=self.base / "pinned-archon",
            archon_bin="/runtime/bin/archon",
        )
        config.workspace.mkdir(parents=True)
        (config.private_lake_packages / "package" / ".git").mkdir(parents=True)
        smoke_payload = json.dumps({
            "dataset_version": RUNNER.DATASET_VERSION,
            "dataset_sha256": RUNNER.DATASET_SHA256,
        })
        with mock.patch.object(RUNNER.subprocess, "run") as run:
            run.side_effect = [
                SimpleNamespace(returncode=0, stdout=smoke_payload),
                SimpleNamespace(returncode=0),
            ]
            code, _seconds = RUNNER._run(
                ["/runtime/bin/archon", "loop", str(config.workspace)],
                config=config,
            )

        self.assertEqual(code, 0)
        self.assertEqual(
            run.call_args_list[0].args[0],
            [
                "/runtime/bin/archon",
                "chemistry-constant",
                "atomic_weight",
                "C",
            ],
        )
        for call in run.call_args_list:
            environment = call.kwargs["env"]
            self.assertEqual(
                environment["PATH"].split(RUNNER.os.pathsep)[0],
                "/runtime/bin",
            )

        with mock.patch.object(RUNNER.subprocess, "run") as run:
            run.return_value = SimpleNamespace(returncode=0, stdout="{}")
            code, _seconds = RUNNER._run(
                ["/runtime/bin/archon", "loop", str(config.workspace)],
                config=config,
            )
        self.assertEqual(code, 126)
        run.assert_called_once()

    def test_run_rejects_empty_private_git_package_set(self) -> None:
        config = RUNNER.Config(campaign_root=self.base / "empty-packages")
        config.workspace.mkdir(parents=True)
        config.private_lake_packages.mkdir()
        with (
            mock.patch.object(RUNNER.subprocess, "run") as run,
            self.assertRaisesRegex(RUNNER.CampaignError, "contains no Git packages"),
        ):
            RUNNER._run(["archon", "--help"], config=config)
        run.assert_not_called()

    def test_run_rejects_symlink_or_non_directory_package_entry(self) -> None:
        for anomaly in ("symlink", "file"):
            with self.subTest(anomaly=anomaly):
                config = RUNNER.Config(campaign_root=self.base / f"invalid-{anomaly}")
                config.workspace.mkdir(parents=True)
                (config.private_lake_packages / "valid" / ".git").mkdir(parents=True)
                invalid = config.private_lake_packages / "invalid"
                if anomaly == "symlink":
                    target = self.base / "external-package"
                    target.mkdir(exist_ok=True)
                    invalid.symlink_to(target, target_is_directory=True)
                else:
                    invalid.write_text("not a package", encoding="utf-8")
                with (
                    mock.patch.object(RUNNER.subprocess, "run") as run,
                    self.assertRaisesRegex(
                        RUNNER.CampaignError, "invalid private Lake package entry"
                    ),
                ):
                    RUNNER._run(["archon", "--help"], config=config)
                run.assert_not_called()

    def test_crnt_metadata_probe_uses_pipe_eof(self) -> None:
        checkout = self.packages / "crnt-lean"
        with mock.patch.object(RUNNER.subprocess, "run") as run:
            run.return_value = SimpleNamespace(stdout="pinned-value\n")
            value = RUNNER._crnt_git_value(checkout, "rev-parse", "HEAD")

        self.assertEqual(value, "pinned-value")
        self.assertIs(run.call_args.kwargs["stdin"], subprocess.PIPE)
        self.assertTrue(run.call_args.kwargs["check"])
        self.assertEqual(
            run.call_args.kwargs["env"]["GIT_CONFIG_GLOBAL"],
            str(checkout / ".git/config"),
        )
        self.assertEqual(
            run.call_args.args[0][-2:],
            ["rev-parse", "HEAD"],
        )

    def test_reused_packages_get_exact_local_path_overrides(self) -> None:
        config = dataclasses.replace(
            self.config,
            campaign_root=self.base / "reused-packages",
            reuse_lake_packages=True,
        )
        validate_patch, copy_patch, configure_patch = self._prepare_patches()
        with validate_patch, copy_patch, configure_patch:
            config, ids = RUNNER._fresh_config(config)
            RUNNER.prepare_workspace(config, ids)

        override_path = config.workspace / RUNNER.PACKAGE_OVERRIDES_REL
        self.assertFalse(override_path.is_symlink())
        self.assertEqual(
            json.loads(override_path.read_text(encoding="utf-8")),
            {
                "schemaVersion": "1.2.0",
                "packages": [{
                    "dir": ".lake/packages/crnt-lean",
                    "inherited": False,
                    "name": "crnt-lean",
                    "scope": "",
                    "type": "path",
                }],
            },
        )
        self.assertEqual(
            (config.workspace / ".lake/packages").resolve(),
            self.packages.resolve(),
        )

    def test_reused_package_overrides_fail_closed_on_snapshot_drift(self) -> None:
        (self.packages / "unlisted-package").mkdir()
        config = dataclasses.replace(
            self.config,
            campaign_root=self.base / "drifted-packages",
            reuse_lake_packages=True,
        )
        validate_patch, copy_patch, configure_patch = self._prepare_patches()
        with (
            validate_patch,
            copy_patch,
            configure_patch,
            self.assertRaisesRegex(
                RUNNER.CampaignError,
                "snapshot does not exactly match the manifest",
            ),
        ):
            config, ids = RUNNER._fresh_config(config)
            RUNNER.prepare_workspace(config, ids)

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
        self.assertEqual(harness["sandbox"], "danger-full-access")
        self.assertEqual(harness["lean_explore_backend"], "hosted")
        self.assertEqual(harness["mcp"], [])
        self.assertNotIn("lean_lsp_mcp_bin", harness)
        self.assertIn("features.code_mode=false", harness["extra_args"])
        self.assertIn("features.code_mode.enabled=false", harness["extra_args"])
        self.assertNotIn("features.code_mode_host=false", harness["extra_args"])
        self.assertIn("features.shell_tool=true", harness["extra_args"])
        self.assertIn("features.multi_agent=false", harness["extra_args"])
        self.assertIn("features.multi_agent_v2=false", harness["extra_args"])
        self.assertEqual(loop["domain_profile"]["name"], "chemistry")
        self.assertEqual(
            loop["domain_profile"]["lean_search_packages"],
            ["Mathlib", "Physlib", "CRNT"],
        )
        self.assertIs(loop["shared_infrastructure"]["enabled"], False)
        self.assertIs(loop["deterministic_review"], True)
        self.assertIs(
            loop["parallel_formalization_review"], config.target_lifecycle,
        )
        self.assertIs(loop["parallel_target_review"], config.target_lifecycle)
        self.assertIs(loop["pipeline_target_review"], config.target_lifecycle)
        self.assertNotIn("base_url_env", harness)
        self.assertNotIn("key_env", harness)
        for key in (
            "max_parallel",
            "review_preflight_jobs",
            "parallel_target_review_jobs",
            "parallel_formalization_review_jobs",
        ):
            self.assertEqual(loop[key], 4)
        self.assertEqual(loop["review_preflight_timeout_sec"], 3600)
        self.assertEqual(loop["max_iterations"], 17)
        self.assertEqual(loop["formalization_review_max_iterations"], 10)
        self.assertEqual(loop["proof_review_max_iterations"], 10)
        self.assertTrue((workspace / ".lake/packages").is_symlink())
        self.assertEqual(
            (workspace / ".lake/packages").resolve(),
            config.private_lake_packages,
        )
        self.assertFalse(
            (workspace / RUNNER.PACKAGE_OVERRIDES_REL).exists(),
        )
        self.assertTrue(config.private_lake_packages.is_dir())
        crnt_index = json.loads(
            (workspace / ".archon/lean-explore/project-index.json").read_text()
        )
        self.assertEqual(crnt_index["package"], "CRNT")
        self.assertEqual(crnt_index["commit"], self.crnt_revision)
        self.assertEqual(crnt_index["repo_url"], self.crnt_url)
        self.assertGreater(crnt_index["declaration_count"], 0)
        self.assertEqual(
            {row["module"] for row in crnt_index["declarations"]},
            {"CRNT.Basic.Reaction"},
        )
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
        self.assertIn("atomically overwrite", formalize)
        self.assertIn(".answer.json", formalize)
        self.assertIn("Semantic Card", formalize)
        self.assertIn("cumulative/overall/repeated-process", formalize)
        self.assertIn("numerator and denominator", formalize)
        self.assertIn("exact unrounded raw value", formalize)
        self.assertIn("source locator", formalize)
        self.assertIn("archon:numeric-reporting-certificate", formalize)
        self.assertIn("reporting_policy_digits", formalize)
        self.assertIn("ReportsAtQuantum", formalize)
        self.assertIn("zero significant-figure report is ambiguous", formalize)
        self.assertIn("numeric_reporting", review)
        self.assertIn("cannot be waived", review)
        self.assertIn("source-first independent derivation", review)
        self.assertIn('"method": "source_first_without_lean"', review)
        self.assertIn("semantic_card_comparison", review)
        self.assertIn("lean_statement_comparison", review)
        self.assertIn("needs_redraft", review)
        self.assertIn("proof of the encoded statement is no", review)
        self.assertIn("evidence that the encoding matches the problem", review)
        self.assertIn("must not run or access the answer\nfreeze", agents)
        self.assertIn("trusted external\ncontroller", agents)
        self.assertIn("cannot read or write the external freeze", protocol)
        self.assertIn("trusted root/controller", protocol)
        self.assertIn("before official-answer\nreveal or scoring", protocol)
        empirical_rule_ids = (
            "aqueous_feiii_phenol_colored_complex",
            "closed_candidate_feiii_phenol_filter",
            "closed_domain_mellite_terminal_residue_candidate_filter",
            "directed_reaction_omitted_protocol_candidate_filter",
            "hexamethylbenzene_cold_kmno4_to_mellitic_acid",
            "mellite_ideal_stoichiometry",
            "mellitic_acid_benzoyl_chloride_to_c12o9",
            "mellitic_acid_p2o5_heating_forms_some_trianhydride",
        )
        for text in (formalize, review):
            normalized = " ".join(text.split())
            self.assertIn(
                '"$ARCHON_CLI_BIN" chemistry-constant atomic_weight <ELEMENT>',
                normalized,
            )
            self.assertIn(
                '"$ARCHON_CLI_BIN" chemistry-constant contest_interpretation '
                '<POLICY_ID>',
                normalized,
            )
            self.assertIn(
                '"$ARCHON_CLI_BIN" chemistry-constant empirical_rule <RULE_ID>',
                normalized,
            )
            self.assertIn("exact `TEMPLATE_ID` allowlist", normalized)
            self.assertEqual(
                normalized.count("binary_two_fragment_electrophilic_addition"),
                1,
            )
            self.assertIn("exact `POLICY_ID` allowlist", normalized)
            self.assertEqual(normalized.count("analogous_halogen_addition"), 1)
            self.assertIn(
                "four-ID baseline list is an exact allowlist", normalized
            )
            self.assertIn("Reference-only empirical-rule IDs", normalized)
            self.assertIn(
                "cannot receive a controller activation receipt", normalized
            )
            self.assertIn(
                "Never borrow a missing protocol condition", normalized
            )
            self.assertIn("dormant Reviewer-requestable bridge IDs", normalized)
            self.assertIn("if even one lacks exact evidence", normalized)
            self.assertIn(
                "Receipt completeness never establishes applicability",
                normalized,
            )
            self.assertIn("ordinary lookup", normalized)
            self.assertIn("controller-built", normalized)
            self.assertIn("exact target and candidate", normalized)
            self.assertIn("Never guess, enumerate, or probe", normalized)
            self.assertIn("unlisted id fails closed", normalized)
            self.assertIn("peer_reviewed_literature", normalized)
            self.assertIn("contest_semantics_policy", normalized)
            self.assertIn("bounded policy", normalized)
            self.assertIn("not a paper or universal empirical law", normalized)
            self.assertIn("automatic_problem_instantiation", normalized)
            self.assertIn("bounded policy into an open-world rule", normalized)
            self.assertIn("base_dataset_sha256", normalized)
            self.assertIn("pinned_rule_record_sha256", normalized)
            self.assertIn("empirical_registry_manifest_sha256", normalized)
            self.assertNotIn("symmetry_guided_benzylic_oxidation", normalized)
            self.assertIn("source.content_sha256", normalized)
            for rule_id in empirical_rule_ids:
                self.assertEqual(normalized.count(rule_id), 1)
            self.assertNotIn("benzylic_oxidation_permanganate", normalized)
            self.assertIn("illustrative, not an allowlist", normalized)
            self.assertIn("source uncertainty could change", normalized)
            self.assertIn("non-empirical contest-semantics policy", normalized)
            self.assertIn("every required cue", normalized)
            self.assertIn("exact problem locator", normalized)
            self.assertIn("does not identify the specific reagent", normalized)
            self.assertIn("must fail closed", normalized)
            self.assertNotIn("`archon chemistry-constant", text)
        self.assertIn(
            ".archon/task_results/IChO2026Problems_problem_<TARGET_ID>.answer.json",
            formalize,
        )
        self.assertIn("display_value", formalize)
        self.assertIn("Do not create any other candidate/answer JSON", formalize)
        self.assertIn("student-visible problem input", agents)
        self.assertIn("may be used only for", agents)
        self.assertIn("may not justify", agents)
        self.assertIn("exam-visible inputs", protocol)
        self.assertIn("never as evidence for the upstream result", protocol)
        self.assertIn("exam-visible fallback", review)
        self.assertIn("require an independent derivation", review)
        self.assertEqual(
            json.loads((workspace / ".mcp.json").read_text()),
            {"mcpServers": {}},
        )
        value["harnesses"]["answer-blind-gpt"]["sandbox"] = "workspace-write"
        (workspace / ".archon/config.json").write_text(
            json.dumps(value), encoding="utf-8"
        )
        with self.assertRaisesRegex(RUNNER.CampaignError, "native non-root Codex"):
            RUNNER._check_native_config(
                workspace,
                max_iterations=self.config.max_iterations,
                review_max_iterations=self.config.review_max_iterations,
                preparation=True,
            )
        value["harnesses"]["answer-blind-gpt"]["sandbox"] = "danger-full-access"
        value.pop("answer_blind")
        (workspace / ".archon/config.json").write_text(
            json.dumps(value), encoding="utf-8"
        )
        with self.assertRaisesRegex(RUNNER.CampaignError, "config is invalid"):
            RUNNER._check_native_config(
                workspace,
                max_iterations=self.config.max_iterations,
                review_max_iterations=self.config.review_max_iterations,
                preparation=True,
            )


    def test_default_fresh_run_prepares_without_starting_loop(self) -> None:
        commands: list[list[str]] = []

        def fake_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            commands.append(command)
            self._write_physics_metadata(config.workspace)
            return 0, 0.25

        patches = self._prepare_patches()
        with (
            patches[0], patches[1], patches[2],
            self._grounding_patch(),
            mock.patch.object(RUNNER.os, "geteuid", return_value=0) as geteuid,
            mock.patch.object(RUNNER, "_run", side_effect=fake_run),
        ):
            result = RUNNER.run_fresh(self.config, start_loop=False)

        geteuid.assert_not_called()
        self.assertEqual(result["status"], "prepared")
        self.assertEqual(len(commands), 1)
        self.assertEqual(commands[0][1], "physics-formalize")
        index = json.loads((self.config.campaign_root / "campaign.json").read_text())
        self.assertEqual(index["max_iterations"], 17)
        self.assertEqual(index["review_max_iterations"], 10)
        self.assertEqual(index["row_count"], 32)
        self.assertEqual(index["max_parallel"], 4)
        self.assertIs(index["target_lifecycle"], False)
        self.assertEqual(index["grounding"], {"complete": 32})
        final_config = json.loads(
            (self.config.campaign_root / "workspace/.archon/config.json").read_text()
        )
        self.assertEqual(
            final_config["loop"]["domain_profile"]["name"], "chemistry-native"
        )
        self.assertEqual(len(self.grounding_calls), 1)
        self.assertEqual(self.grounding_calls[0]["backend"], "hosted")
        self.assertEqual(
            self.grounding_calls[0]["packages"],
            ("Mathlib", "Physlib", "CRNT"),
        )
        self.assertEqual(len(self.grounding_calls[0]["lean_files"]), 32)
        chapters = self.config.campaign_root / "workspace/blueprint/src/chapters"
        for chapter in chapters.glob("*.tex"):
            self.assertNotIn("archon:source-report", chapter.read_text())
            self.assertNotIn("archon:physics", chapter.read_text())
            self.assertEqual(chapter.read_text().count("% archon:chemistry"), 1)

    def test_initial_grounding_accepts_incomplete_evidence_and_counts_it(self) -> None:
        workspace = self.base / "grounding-fail-closed" / "workspace"
        workspace.mkdir(parents=True)
        config = RUNNER.Config(campaign_root=workspace.parent)
        reports = []
        targets = RUNNER._targets(self.ids)
        for offset, target in enumerate(targets):
            lean_file = workspace / target
            report_path = (
                workspace / ".archon/task_results"
                / RUNNER.grounding_report_name(workspace, lean_file)
            )
            report_path.parent.mkdir(parents=True, exist_ok=True)
            status = "incomplete" if offset == len(targets) - 1 else "complete"
            report_path.write_text(
                f"- Grounding status: {status}\n"
                "- Search backend: hosted\n"
                f"- Input fingerprint: sha256:{'a' * 64}\n"
                "- Packages searched: Mathlib, Physlib, CRNT\n",
                encoding="utf-8",
            )
            reports.append(SimpleNamespace(
                lean_file=lean_file,
                report_path=report_path,
                is_complete=status == "complete",
            ))

        with mock.patch.object(
            RUNNER, "run_physics_grounding", return_value=reports
        ):
            counts = RUNNER._run_initial_grounding(config, self.ids)

        self.assertEqual(counts, {"complete": 31, "incomplete": 1})
        warning = config.log_path.read_text(encoding="utf-8")
        self.assertIn("1 target(s) incomplete", warning)
        self.assertIn("needs_redraft", warning)

    def test_initial_grounding_fails_closed_on_missing_or_wrong_scope(self) -> None:
        workspace = self.base / "grounding-invalid" / "workspace"
        workspace.mkdir(parents=True)
        config = RUNNER.Config(campaign_root=workspace.parent)
        reports = self._fake_grounding(
            workspace,
            lean_files=[workspace / target for target in RUNNER._targets(self.ids)],
        )
        outside = workspace / "wrong-scope.md"
        outside.write_bytes(reports[-1].report_path.read_bytes())
        wrong_scope = [*reports[:-1], SimpleNamespace(
            lean_file=reports[-1].lean_file,
            report_path=outside,
            is_complete=True,
        )]

        for anomaly, returned in (("missing", reports[:-1]), ("scope", wrong_scope)):
            with self.subTest(anomaly=anomaly), mock.patch.object(
                RUNNER, "run_physics_grounding", return_value=returned
            ), self.assertRaisesRegex(RUNNER.CampaignError, "grounding"):
                RUNNER._run_initial_grounding(config, self.ids)

    def test_resume_fails_closed_on_config_marker_or_crnt_index_tampering(self) -> None:
        for anomaly in ("config", "timeout", "marker", "index", "manifest", "checkout"):
            with self.subTest(anomaly=anomaly):
                fresh = dataclasses.replace(
                    self.config,
                    campaign_root=self.base / f"resume-invalid-{anomaly}",
                )
                self._prepare_only(fresh)
                workspace = fresh.workspace
                if anomaly == "config":
                    path = workspace / ".archon/config.json"
                    payload = json.loads(path.read_text())
                    payload["loop"]["domain_profile"]["lean_search_packages"] = [
                        "Mathlib", "Physlib", "WrongPackage",
                    ]
                    path.write_text(json.dumps(payload), encoding="utf-8")
                elif anomaly == "timeout":
                    path = workspace / ".archon/config.json"
                    payload = json.loads(path.read_text())
                    payload["loop"]["review_preflight_timeout_sec"] = 300
                    path.write_text(json.dumps(payload), encoding="utf-8")
                elif anomaly == "marker":
                    path = next((workspace / "blueprint/src/chapters").glob("*.tex"))
                    path.write_text(
                        path.read_text().replace(
                            "% archon:chemistry", "% archon:physics"
                        ),
                        encoding="utf-8",
                    )
                else:
                    if anomaly == "index":
                        path = workspace / RUNNER.CRNT_INDEX_REL
                        payload = json.loads(path.read_text())
                        payload["commit"] = "0" * 40
                        path.write_text(json.dumps(payload), encoding="utf-8")
                    elif anomaly == "manifest":
                        path = workspace / "lake-manifest.json"
                        payload = json.loads(path.read_text())
                        payload["packages"][0]["rev"] = "0" * 40
                        path.write_text(json.dumps(payload), encoding="utf-8")
                    else:
                        subprocess.run(
                            [
                                "git", "remote", "set-url", "origin",
                                "https://example.invalid/wrong-crnt",
                            ],
                            cwd=fresh.private_lake_packages / "crnt-lean",
                            check=True,
                        )

                resumed = RUNNER.Config(
                    campaign_root=fresh.campaign_root,
                    archon_bin=fresh.archon_bin,
                    max_iterations=fresh.max_iterations,
                )
                with (
                    mock.patch.object(RUNNER, "_run") as run,
                    self.assertRaises(RUNNER.CampaignError),
                ):
                    RUNNER.resume_campaign(resumed)
                run.assert_not_called()

    def test_dry_run_is_permitted_as_root(self) -> None:
        validate = self._prepare_patches()[0]
        with (
            validate,
            mock.patch.object(RUNNER.os, "geteuid", return_value=0) as geteuid,
        ):
            result = RUNNER.dry_run(self.config, include_loop=True)

        geteuid.assert_not_called()
        self.assertEqual(result["status"], "dry-run")

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
        with (
            patches[0], patches[1], patches[2],
            self._grounding_patch(),
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
            mock.patch.object(RUNNER, "_run", side_effect=fake_run),
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

    def test_native_success_rejects_extra_gate_target(self) -> None:
        workspace = self.base / "native-extra-target"
        (workspace / ".archon").mkdir(parents=True)
        self._write_success_state(workspace)
        gate_path = workspace / ".archon/proof-review-gate.json"
        gate = json.loads(gate_path.read_text(encoding="utf-8"))
        gate["targets"]["Problems/Unexpected.lean"] = {"status": "solved"}
        gate_path.write_text(json.dumps(gate), encoding="utf-8")

        result = RUNNER.native_summary(workspace, self.ids)

        self.assertFalse(result["complete"])
        self.assertEqual(result["proof_review"], {"solved": 32})

    def test_native_success_rejects_older_build_after_interrupted_iteration(self) -> None:
        workspace = self.base / "stale-native-state"
        (workspace / ".archon").mkdir(parents=True)
        self._write_success_state(workspace)
        newer = workspace / ".archon/logs/iter-002/meta.json"
        newer.parent.mkdir(parents=True)
        newer.write_text(json.dumps({
            "iteration": 2,
            "plan": {"status": "running"},
        }), encoding="utf-8")

        result = RUNNER.native_summary(workspace, self.ids)

        self.assertFalse(result["complete"])
        self.assertIsNone(result["lake_build_ok"])
        self.assertIsNone(result["sorry_count"])

    def test_nonzero_loop_cannot_reuse_an_old_complete_summary(self) -> None:
        config = RUNNER.Config(campaign_root=self.base / "failed-campaign")
        config.campaign_root.mkdir()
        config.workspace.mkdir()
        (config.workspace / ".archon").mkdir()
        self._write_success_state(config.workspace)
        index = {"pipeline": RUNNER.PIPELINE, "status": "running"}
        with (
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
            mock.patch.object(RUNNER, "_run", return_value=(1, 0.1)),
        ):
            result = RUNNER._run_loop(config, self.ids, index, resume=False)
        self.assertEqual(result["status"], "failed")

    def test_model_loop_refuses_root_before_starting_process(self) -> None:
        config = RUNNER.Config(campaign_root=self.base / "root-campaign")
        index = {"pipeline": RUNNER.PIPELINE, "status": "prepared"}
        with (
            mock.patch.object(RUNNER.os, "geteuid", return_value=0),
            mock.patch.object(RUNNER, "_run") as run,
            self.assertRaisesRegex(RUNNER.CampaignError, "non-root solver UID"),
        ):
            RUNNER._run_loop(config, self.ids, index, resume=False)
        run.assert_not_called()
        self.assertEqual(index["status"], "prepared")

    def test_prepared_campaign_starts_without_repreparing(self) -> None:
        patches = self._prepare_patches()

        def prepare_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            self._write_physics_metadata(config.workspace)
            return 0, 0.1

        with (
            patches[0], patches[1], patches[2], self._grounding_patch(),
            mock.patch.object(RUNNER, "_run", side_effect=prepare_run),
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
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
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

        with (
            patches[0], patches[1], patches[2], self._grounding_patch(),
            mock.patch.object(RUNNER, "_run", side_effect=prepare_run),
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

        with (
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
            mock.patch.object(RUNNER, "_run", side_effect=resume_run),
        ):
            result = RUNNER.resume_campaign(resume_config)

        self.assertIn("--resume", seen[0])
        self.assertNotIn("--from", seen[0])
        self.assertEqual(result["status"], "succeeded")

    def test_resume_idempotently_records_an_already_complete_native_state(self) -> None:
        self._prepare_only()
        self._write_success_state(self.config.workspace)
        index_path = self.config.index_path
        payload = json.loads(index_path.read_text())
        payload.update({
            "status": "incomplete",
            "phase": "resume",
            "returncode": 7,
            "duration_seconds": 123.5,
            "audit": {"proof_review_verdicts": 32},
        })
        index_path.write_text(json.dumps(payload), encoding="utf-8")
        resume_config = RUNNER.Config(
            campaign_root=self.config.campaign_root,
            archon_bin=self.config.archon_bin,
            max_iterations=self.config.max_iterations,
        )

        with (
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000) as geteuid,
            mock.patch.object(RUNNER, "_run") as run,
            mock.patch.object(RUNNER, "_utcnow", return_value="2026-08-13T00:00:00Z"),
        ):
            first = RUNNER.resume_campaign(resume_config)
            second = RUNNER.resume_campaign(resume_config)

        run.assert_not_called()
        geteuid.assert_not_called()
        self.assertEqual(first, second)
        self.assertEqual(second["status"], "succeeded")
        self.assertEqual(second["phase"], "complete")
        self.assertEqual(second["returncode"], 0)
        self.assertTrue(second["native"]["complete"])
        progress = self.config.workspace / ".archon/PROGRESS.md"
        self.assertIn("\ncomplete\n", progress.read_text(encoding="utf-8"))
        self.assertEqual(second["duration_seconds"], 123.5)
        self.assertEqual(second["audit"], {"proof_review_verdicts": 32})
        self.assertEqual(json.loads(index_path.read_text()), second)

    def test_resume_runs_archon_when_any_native_target_is_unsettled(self) -> None:
        unsettled_statuses = (
            "retry",
            "needs_redraft",
            "blocked_infrastructure",
            "proof_review_exhausted",
        )
        for status in unsettled_statuses:
            with self.subTest(status=status):
                fresh = dataclasses.replace(
                    self.config,
                    campaign_root=self.base / f"resume-unsettled-{status}",
                )
                self._prepare_only(fresh)
                self._write_success_state(fresh.workspace)
                gate_path = fresh.workspace / ".archon/proof-review-gate.json"
                gate = json.loads(gate_path.read_text())
                gate["targets"][RUNNER._targets(self.ids)[0]]["status"] = status
                gate_path.write_text(json.dumps(gate), encoding="utf-8")
                index_path = fresh.index_path
                payload = json.loads(index_path.read_text())
                payload["status"] = "incomplete"
                index_path.write_text(json.dumps(payload), encoding="utf-8")
                resume_config = RUNNER.Config(
                    campaign_root=fresh.campaign_root,
                    archon_bin=fresh.archon_bin,
                    max_iterations=fresh.max_iterations,
                )

                with (
                    mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
                    mock.patch.object(RUNNER, "_run", return_value=(1, 0.2)) as run,
                ):
                    result = RUNNER.resume_campaign(resume_config)

                run.assert_called_once()
                command = run.call_args.args[0]
                self.assertIn("--resume", command)
                self.assertEqual(result["status"], "failed")
                self.assertFalse(result["native"]["complete"])
                self.assertEqual(result["native"]["proof_review"][status], 1)

    def test_review_budget_propagates_and_resume_fails_closed(self) -> None:
        config = dataclasses.replace(
            self.config,
            campaign_root=self.base / "review-budget-three",
            max_iterations=5,
            review_max_iterations=3,
        )
        self._prepare_only(config)

        native_path = config.workspace / ".archon/config.json"
        native = json.loads(native_path.read_text(encoding="utf-8"))
        loop_config = native["loop"]
        self.assertEqual(loop_config["max_iterations"], 5)
        self.assertEqual(loop_config["formalization_review_max_iterations"], 3)
        self.assertEqual(loop_config["proof_review_max_iterations"], 3)

        command = RUNNER.loop_command(config, resume=False)
        self.assertEqual(command[command.index("--max-iterations") + 1], "5")
        self.assertEqual(
            command[
                command.index("--formalization-review-max-iterations") + 1
            ],
            "3",
        )
        self.assertEqual(
            command[command.index("--proof-review-max-iterations") + 1], "3"
        )

        index_path = config.index_path
        original_index = json.loads(index_path.read_text(encoding="utf-8"))
        self.assertEqual(original_index["max_iterations"], 5)
        self.assertEqual(original_index["review_max_iterations"], 3)

        forgotten = RUNNER.Config(
            campaign_root=config.campaign_root,
            archon_bin=config.archon_bin,
            max_iterations=config.max_iterations,
        )
        with (
            mock.patch.object(RUNNER, "_run") as run,
            self.assertRaisesRegex(
                RUNNER.CampaignError,
                "unexpected formalization_review_max_iterations",
            ),
        ):
            RUNNER.resume_campaign(forgotten)
        run.assert_not_called()

        matching = dataclasses.replace(
            forgotten, review_max_iterations=config.review_max_iterations
        )
        for key in (
            "max_iterations",
            "formalization_review_max_iterations",
            "proof_review_max_iterations",
        ):
            with self.subTest(native_key=key):
                tampered_native = json.loads(json.dumps(native))
                tampered_native["loop"][key] += 1
                native_path.write_text(
                    json.dumps(tampered_native), encoding="utf-8"
                )
                with self.assertRaisesRegex(
                    RUNNER.CampaignError, f"unexpected {key}"
                ):
                    RUNNER._resume_config(matching)
        native_path.write_text(json.dumps(native), encoding="utf-8")

        for field, value in (
            ("max_iterations", None),
            ("max_iterations", 6),
            ("review_max_iterations", None),
            ("review_max_iterations", 4),
        ):
            with self.subTest(receipt_field=field, receipt_value=value):
                tampered = dict(original_index)
                if value is None:
                    tampered.pop(field)
                else:
                    tampered[field] = value
                index_path.write_text(json.dumps(tampered), encoding="utf-8")
                with (
                    mock.patch.object(RUNNER, "_run") as run,
                    self.assertRaisesRegex(
                        RUNNER.CampaignError, "prepared campaign value"
                    ),
                ):
                    RUNNER.resume_campaign(matching)
                run.assert_not_called()
        index_path.write_text(json.dumps(original_index), encoding="utf-8")

        parser = RUNNER._parser()
        defaults = parser.parse_args([
            "--campaign-root", str(self.base / "review-default"), "--dry-run",
        ])
        explicit = parser.parse_args([
            "--campaign-root", str(self.base / "review-explicit"),
            "--review-max-iterations", "3", "--dry-run",
        ])
        self.assertEqual(defaults.review_max_iterations, 10)
        self.assertEqual(explicit.review_max_iterations, 3)
        self.assertIn("--review-max-iterations", parser.format_help())
        self.assertIn("repeat the prepared value on resume", parser.format_help())

    def test_iteration_budgets_reject_zero_and_bool_fresh_and_resume(self) -> None:
        prepared = dataclasses.replace(
            self.config, campaign_root=self.base / "valid-budget-for-resume"
        )
        self._prepare_only(prepared)
        for field in ("max_iterations", "review_max_iterations"):
            for value in (0, True):
                with self.subTest(phase="fresh", field=field, value=value):
                    invalid = dataclasses.replace(
                        self.config,
                        campaign_root=self.base / f"invalid-{field}-{value}",
                        **{field: value},
                    )
                    with self.assertRaisesRegex(
                        RUNNER.CampaignError, f"{field} must be a positive integer"
                    ):
                        RUNNER._fresh_config(invalid)
                with self.subTest(phase="resume", field=field, value=value):
                    invalid = dataclasses.replace(prepared, **{field: value})
                    with self.assertRaisesRegex(
                        RUNNER.CampaignError, f"{field} must be a positive integer"
                    ):
                        RUNNER._resume_config(invalid)

    def test_target_lifecycle_cli_is_explicit_opt_in(self) -> None:
        parser = RUNNER._parser()
        default = parser.parse_args([
            "--campaign-root", str(self.base / "default-lifecycle"),
            "--dry-run",
        ])
        enabled = parser.parse_args([
            "--campaign-root", str(self.base / "target-lifecycle"),
            "--target-lifecycle",
            "--dry-run",
        ])

        self.assertIs(default.target_lifecycle, False)
        self.assertIs(enabled.target_lifecycle, True)
        self.assertIn("--target-lifecycle", parser.format_help())
        self.assertIn("repeat this", parser.format_help())
        self.assertIn("flag on resume", parser.format_help())
        with mock.patch("sys.stderr"), self.assertRaises(SystemExit):
            parser.parse_args([
                "--campaign-root", str(self.base / "invalid-lifecycle"),
                "--target-lifecycle=false",
            ])
        with self.assertRaisesRegex(
            RUNNER.CampaignError, "target_lifecycle must be a boolean"
        ):
            RUNNER._fresh_config(dataclasses.replace(
                self.config,
                campaign_root=self.base / "non-bool-lifecycle",
                target_lifecycle=1,
            ))

    def test_legacy_default_receipt_is_normalized_on_resume(self) -> None:
        config = dataclasses.replace(
            self.config,
            campaign_root=self.base / "legacy-default-receipt",
        )
        self._prepare_only(config)
        index_path = config.index_path
        index = json.loads(index_path.read_text())
        del index["target_lifecycle"]
        index_path.write_text(json.dumps(index), encoding="utf-8")

        resume_config = RUNNER.Config(
            campaign_root=config.campaign_root,
            archon_bin=config.archon_bin,
            max_iterations=config.max_iterations,
        )

        def fake_resume(
            _command: list[str], *, config: RUNNER.Config
        ) -> tuple[int, float]:
            self._write_success_state(config.workspace)
            return 0, 0.25

        with (
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
            mock.patch.object(RUNNER, "_run", side_effect=fake_resume),
        ):
            result = RUNNER.resume_campaign(resume_config)

        self.assertEqual(result["status"], "succeeded")
        self.assertIs(result["target_lifecycle"], False)
        persisted = json.loads(index_path.read_text())
        self.assertIs(persisted["target_lifecycle"], False)

    def test_target_lifecycle_opt_in_is_configured_and_resume_is_fail_closed(self) -> None:
        config = dataclasses.replace(
            self.config,
            campaign_root=self.base / "target-lifecycle-enabled",
            max_parallel=7,
            target_lifecycle=True,
        )
        self._prepare_only(config)

        native_config = json.loads(
            (config.workspace / ".archon/config.json").read_text()
        )
        loop = native_config["loop"]
        for key in (
            "parallel_formalization_review",
            "parallel_target_review",
            "pipeline_target_review",
        ):
            self.assertIs(loop[key], True)
        for key in (
            "review_preflight_jobs",
            "parallel_target_review_jobs",
            "parallel_formalization_review_jobs",
        ):
            self.assertEqual(loop[key], 7)

        index_path = config.index_path
        index = json.loads(index_path.read_text())
        self.assertIs(index["target_lifecycle"], True)

        forgotten_flag = RUNNER.Config(
            campaign_root=config.campaign_root,
            archon_bin=config.archon_bin,
            max_iterations=config.max_iterations,
            max_parallel=config.max_parallel,
        )
        with (
            mock.patch.object(RUNNER, "_run") as run,
            self.assertRaisesRegex(
                RUNNER.CampaignError, "--target-lifecycle must match"
            ),
        ):
            RUNNER.resume_campaign(forgotten_flag)
        run.assert_not_called()

        matching_resume = dataclasses.replace(
            forgotten_flag,
            target_lifecycle=True,
        )
        index["target_lifecycle"] = "true"
        index_path.write_text(json.dumps(index), encoding="utf-8")
        with (
            mock.patch.object(RUNNER, "_run") as run,
            self.assertRaisesRegex(
                RUNNER.CampaignError, "invalid target_lifecycle"
            ),
        ):
            RUNNER.resume_campaign(matching_resume)
        run.assert_not_called()

        index["target_lifecycle"] = False
        index_path.write_text(json.dumps(index), encoding="utf-8")
        with (
            mock.patch.object(RUNNER, "_run") as run,
            self.assertRaisesRegex(
                RUNNER.CampaignError, "prepared campaign value"
            ),
        ):
            RUNNER.resume_campaign(matching_resume)
        run.assert_not_called()

        index["target_lifecycle"] = True
        index_path.write_text(json.dumps(index), encoding="utf-8")
        seen: list[list[str]] = []

        def fake_resume(
            command: list[str], *, config: RUNNER.Config
        ) -> tuple[int, float]:
            seen.append(command)
            self._write_success_state(config.workspace)
            return 0, 0.25

        with (
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
            mock.patch.object(RUNNER, "_run", side_effect=fake_resume),
        ):
            result = RUNNER.resume_campaign(matching_resume)

        self.assertEqual(result["status"], "succeeded")
        self.assertIs(result["target_lifecycle"], True)
        self.assertEqual(len(seen), 1)
        self.assertIn("--from", seen[0])
        self.assertNotIn("--resume", seen[0])

    def test_max_parallel_32_propagates_to_config_command_and_receipt(self) -> None:
        config = dataclasses.replace(
            self.config,
            campaign_root=self.base / "parallel-32",
            max_parallel=32,
        )
        commands: list[list[str]] = []

        def fake_run(command: list[str], *, config: RUNNER.Config) -> tuple[int, float]:
            commands.append(command)
            self._write_physics_metadata(config.workspace)
            return 0, 0.25

        patches = self._prepare_patches()
        with (
            patches[0], patches[1], patches[2],
            self._grounding_patch(),
            mock.patch.object(RUNNER, "_run", side_effect=fake_run),
        ):
            result = RUNNER.run_fresh(config, start_loop=False)

        self.assertEqual(result["status"], "prepared")
        self.assertEqual(result["max_parallel"], 32)
        native_config = json.loads(
            (config.workspace / ".archon/config.json").read_text()
        )
        for key in (
            "max_parallel",
            "review_preflight_jobs",
            "parallel_target_review_jobs",
            "parallel_formalization_review_jobs",
        ):
            self.assertEqual(native_config["loop"][key], 32)

        loop = RUNNER.loop_command(config, resume=False)
        self.assertEqual(loop[loop.index("--max-parallel") + 1], "32")
        parsed = RUNNER._parser().parse_args([
            "--campaign-root", str(self.base / "cli"),
            "--max-parallel", "32",
            "--dry-run",
        ])
        self.assertEqual(parsed.max_parallel, 32)

        with self.assertRaisesRegex(
            RUNNER.CampaignError, "unexpected max_parallel"
        ):
            RUNNER.resume_campaign(
                RUNNER.Config(
                    campaign_root=config.campaign_root,
                    max_iterations=config.max_iterations,
                    review_max_iterations=config.review_max_iterations,
                )
            )

        resume_commands: list[list[str]] = []

        def fake_resume(
            command: list[str], *, config: RUNNER.Config
        ) -> tuple[int, float]:
            resume_commands.append(command)
            self._write_success_state(config.workspace)
            return 0, 0.25

        matching_resume = RUNNER.Config(
            campaign_root=config.campaign_root,
            archon_bin=config.archon_bin,
            max_iterations=config.max_iterations,
            max_parallel=32,
        )
        with (
            mock.patch.object(RUNNER.os, "geteuid", return_value=1000),
            mock.patch.object(RUNNER, "_run", side_effect=fake_resume),
        ):
            resumed = RUNNER.resume_campaign(matching_resume)

        self.assertEqual(resumed["status"], "succeeded")
        self.assertEqual(len(resume_commands), 1)
        resumed_loop = resume_commands[0]
        self.assertEqual(
            resumed_loop[resumed_loop.index("--max-parallel") + 1], "32"
        )
        self.assertIn("--from", resumed_loop)
        self.assertNotIn("--resume", resumed_loop)

        index_path = config.index_path
        tampered_index = json.loads(index_path.read_text())
        tampered_index["max_parallel"] = 31
        index_path.write_text(json.dumps(tampered_index), encoding="utf-8")
        with (
            mock.patch.object(RUNNER, "_run") as run,
            self.assertRaisesRegex(
                RUNNER.CampaignError, "prepared campaign value"
            ),
        ):
            RUNNER.resume_campaign(matching_resume)
        run.assert_not_called()

        for value in (0, 33, True, 2.5):
            with self.subTest(value=value), self.assertRaisesRegex(
                RUNNER.CampaignError, "between 1 and 32"
            ):
                RUNNER._fresh_config(
                    dataclasses.replace(
                        self.config,
                        campaign_root=self.base / f"invalid-parallel-{value}",
                        max_parallel=value,
                    )
                )


if __name__ == "__main__":
    unittest.main()
