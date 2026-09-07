from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import stat
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_ipho_answer_blind_gpt_campaign.py"
)
SPEC = importlib.util.spec_from_file_location("ipho_gpt_campaign", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IphoGptCampaignTests(unittest.TestCase):
    def test_required_gpt_profile_matches_configurator(self):
        config_script = SCRIPT.with_name("configure_ipho_answer_blind_workspace.py")
        spec = importlib.util.spec_from_file_location("ipho_gpt_config_fixture", config_script)
        assert spec and spec.loader
        configurator = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(configurator)
        generated = configurator.build_archon_config(
            variant="gpt", max_objectives=28, max_parallel=32
        )
        descriptor = generated["harnesses"]["answer-blind-gpt"]
        self.assertEqual(descriptor["extra_args"], list(MODULE.GPT_REQUIRED_EXTRA_ARGS))
        self.assertEqual(descriptor["sandbox"], "danger-full-access")

    def test_prepared_frontier_requires_all_28_reports_chapters_and_objectives(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = Path(raw)
            (workspace / "ipho_2026_source").mkdir()
            (workspace / "reports/ipho_2026").mkdir(parents=True)
            (workspace / "blueprint/src/chapters").mkdir(parents=True)
            (workspace / ".archon").mkdir()
            config = {
                "answer_blind": {
                    "authority": "problem-only",
                    "official_answer_seen": False,
                },
                "harnesses": {
                    "answer-blind-gpt": {
                        "runner": "codex",
                        "model": "gpt-5.6-sol",
                        "effort": "max",
                        "ignore_user_config": True,
                        "ephemeral": True,
                        "sandbox": "danger-full-access",
                        "lean_explore_backend": "local",
                        "mcp": ["lean-explore"],
                        "extra_args": list(MODULE.GPT_REQUIRED_EXTRA_ARGS),
                    }
                },
                "loop": {
                    "harness": "answer-blind-gpt",
                    "model": "gpt-5.6-sol",
                    "max_parallel": 32,
                    "max_objectives": 28,
                    "domain_profile": {
                        "lean_search_packages": ["Mathlib", "Physlib"]
                    },
                },
            }
            (workspace / ".archon/config.json").write_text(json.dumps(config) + "\n")
            for destination_rel, source_rel in MODULE.WORKSPACE_PROMPT_SOURCES.items():
                destination = workspace / destination_rel
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes((MODULE.REPOSITORY_ROOT / source_rel).read_bytes())
            ids = [f"fixture_{number:02d}" for number in range(28)]
            bundle = workspace / "ipho_2026_source/questions_only.jsonl"
            rows = [
                {
                    "id": target_id,
                    "evaluation_mode": "answer_blind",
                    "official_answer_seen": False,
                }
                for target_id in ids
            ]
            bundle.write_text("".join(json.dumps(row) + "\n" for row in rows))
            objectives: list[str] = []
            for target_id, row in zip(ids, rows, strict=True):
                report_rel = f"reports/ipho_2026/problem_{target_id}.source.json"
                digest = MODULE._blind_record_sha256(row)
                (workspace / report_rel).write_text(
                    json.dumps(
                        {
                            "evaluation_mode": "answer_blind",
                            "official_answer_seen": False,
                            "output_lean": f"IPhO2026Problems/problem_{target_id}.lean",
                            "source_report": report_rel,
                            "blind_record_sha256": digest,
                            "entry": {
                                **row,
                                "blind_record_sha256": digest,
                            },
                        }
                    )
                    + "\n"
                )
                (workspace / f"blueprint/src/chapters/IPhO2026Problems_problem_{target_id}.tex").write_text("% fixture\n")
                objectives.append(
                    f"- **`IPhO2026Problems/problem_{target_id}.lean`** — fixture"
                )
            (workspace / ".archon/PROGRESS.md").write_text(
                "## Current Stage\n\nautoformalize\n\n## Current Objectives\n\n"
                + "\n".join(objectives)
                + "\n"
            )

            self.assertEqual(
                MODULE._validate_prepared_formalization_frontier(workspace),
                {
                    "target_count": 28,
                    "stage": "autoformalize",
                    "harness": "answer-blind-gpt",
                },
            )
            config_path = workspace / ".archon/config.json"
            invalid_config = json.loads(config_path.read_text())
            invalid_config["harnesses"]["answer-blind-gpt"]["extra_args"].pop()
            config_path.write_text(json.dumps(invalid_config) + "\n")
            with self.assertRaisesRegex(MODULE.CampaignError, "pinned Codex profile"):
                MODULE._validate_prepared_formalization_frontier(workspace)
            config_path.write_text(json.dumps(config) + "\n")
            physics_prompt = workspace / ".archon/prover-modes/physics.md"
            physics_prompt.write_text(physics_prompt.read_text() + "\n% stale\n")
            with self.assertRaisesRegex(MODULE.CampaignError, "stale or missing"):
                MODULE._validate_prepared_formalization_frontier(workspace)
            physics_prompt.write_bytes(
                (
                    MODULE.REPOSITORY_ROOT
                    / MODULE.WORKSPACE_PROMPT_SOURCES[
                        ".archon/prover-modes/physics.md"
                    ]
                ).read_bytes()
            )
            last_report = workspace / "reports/ipho_2026/problem_fixture_27.source.json"
            invalid = json.loads(last_report.read_text())
            invalid["evaluation_mode"] = "visible"
            last_report.write_text(json.dumps(invalid) + "\n")
            with self.assertRaisesRegex(MODULE.CampaignError, "invalid_reports=1"):
                MODULE._validate_prepared_formalization_frontier(workspace)
            last_report.unlink()
            with self.assertRaisesRegex(MODULE.CampaignError, "reports=1"):
                MODULE._validate_prepared_formalization_frontier(workspace)

    def test_prepared_frontier_rejects_non_gpt_harness(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = Path(raw)
            (workspace / ".archon").mkdir()
            (workspace / "ipho_2026_source").mkdir()
            (workspace / "ipho_2026_source/questions_only.jsonl").write_text("\n")
            (workspace / ".archon/PROGRESS.md").write_text("autoformalize\n")
            (workspace / ".archon/config.json").write_text(
                json.dumps({"loop": {"harness": "answer-blind-kimi"}}) + "\n"
            )
            with self.assertRaisesRegex(MODULE.CampaignError, "pinned Codex profile"):
                MODULE._validate_prepared_formalization_frontier(workspace)

    def test_defaults_are_full_ipho_with_32_way_capacity(self):
        args = MODULE._parser().parse_args(
            [
                "--codex-home-template",
                "/controller/codex",
                "--controller-dir",
                "/controller/run",
                "--workspace",
                "/solver",
                "--dependency-root",
                "/dependencies",
                "--private-home",
                "/private/home",
                "--private-tmp",
                "/private/tmp",
                "--run-id",
                "ipho-gpt-r1",
                "--solver-user",
                "iphosolver",
                "--lean-explore-hf-cache",
                "/cache/hf",
            ]
        )
        self.assertEqual(args.max_objectives, 28)
        self.assertEqual(args.max_parallel, 32)
        self.assertEqual(args.max_iterations, 4)
        self.assertEqual(args.runtime_root, MODULE.SEALED_RUNTIME)

    def test_archon_command_is_gpt_physics_batch_not_icho_full32(self):
        argv = MODULE._archon_argv(
            Path("/runtime"),
            max_iterations=4,
            max_parallel=32,
            max_objectives=28,
        )
        self.assertEqual(argv[argv.index("--model") + 1], "gpt-5.6-sol")
        self.assertEqual(argv[argv.index("--max-parallel") + 1], "32")
        self.assertEqual(argv[argv.index("--max-objectives") + 1], "28")
        self.assertEqual(
            argv[argv.index("--proof-review-max-iterations") + 1], "4"
        )
        self.assertNotIn("IChO2026Problems", " ".join(argv))

    def test_copies_only_unique_auth_json(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            template = root / "template"
            home = root / "home"
            template.mkdir(mode=0o700)
            template.chmod(0o701)
            home.mkdir(mode=0o700)
            auth = template / "auth.json"
            auth.write_text('{"tokens":{"access_token":"fixture"}}\n')
            auth.chmod(0o600)
            isolation = SimpleNamespace(
                _plain_directory=lambda path, **_kwargs: Path(path).resolve(strict=True)
            )
            source = MODULE._validate_codex_auth_template(isolation, template)
            destination_home = MODULE._copy_minimal_codex_auth(
                source,
                home,
                SimpleNamespace(uid=os.getuid(), gid=os.getgid()),
            )
            copied = destination_home / "auth.json"
            self.assertEqual(copied.read_bytes(), auth.read_bytes())
            self.assertNotEqual(copied.stat().st_ino, auth.stat().st_ino)
            self.assertEqual(stat.S_IMODE(copied.stat().st_mode), 0o600)
            self.assertEqual(
                sorted(path.relative_to(home).as_posix() for path in home.rglob("*")),
                [".codex", ".codex/auth.json"],
            )

    def test_run_uses_existing_jail_https_and_no_provider_env_secret(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = {
                name: root / name
                for name in (
                    "workspace",
                    "dependency",
                    "runtime",
                    "controller",
                    "cache",
                    "hf-cache",
                    "codex-template",
                )
            }
            for path in paths.values():
                path.mkdir(mode=0o700)
            (paths["runtime"] / "bin").mkdir()
            codex = paths["runtime"] / "bin/codex"
            codex.write_text("#!/bin/sh\nexit 0\n")
            codex.chmod(0o555)
            auth = paths["codex-template"] / "auth.json"
            auth.write_text("{}\n")
            auth.chmod(0o600)
            home = root / "private-home"
            temporary = root / "private-tmp"
            args = argparse.Namespace(
                codex_home_template=paths["codex-template"],
                controller_dir=paths["controller"],
                workspace=paths["workspace"],
                dependency_root=paths["dependency"],
                private_home=home,
                private_tmp=temporary,
                run_id="ipho-gpt-r1",
                solver_user="iphosolver",
                runtime_root=paths["runtime"],
                lean_explore_cache=paths["cache"],
                lean_explore_hf_cache=paths["hf-cache"],
                lean_explore_site_packages=None,
                max_iterations=4,
                max_parallel=32,
                max_objectives=28,
                timeout_s=60,
            )
            policy = SimpleNamespace(
                receipt=lambda **kwargs: {"https": True, **kwargs}
            )
            calls: dict[str, object] = {}

            def harden_solver_workspace(**kwargs: object) -> dict[str, object]:
                home.mkdir(mode=0o700)
                temporary.mkdir(mode=0o700)
                return {"variant": kwargs["variant"]}

            def build_landlock_policy(**kwargs: object):
                calls["policy"] = kwargs
                return policy

            def run_confined_command(**kwargs: object):
                calls["command"] = kwargs
                Path(kwargs["log_path"]).write_text("fixture log\n")
                return SimpleNamespace(
                    started_at="start",
                    ended_at="end",
                    exit_code=0,
                    timed_out=False,
                    solver_stopped=True,
                    descendants_stopped=True,
                    confinement_error=None,
                    dedicated_uid_quiescence={"quiescent_after": True},
                    probes={},
                    connected_fd_injection_count=0,
                    seccomp_supervisor_fail_closed=True,
                    seccomp_supervisor_stopped=True,
                )

            sealed = SimpleNamespace(
                _identity=lambda _user: SimpleNamespace(
                    uid=12345, gid=12345, user="iphosolver"
                ),
                harden_solver_workspace=harden_solver_workspace,
                build_landlock_policy=build_landlock_policy,
                _minimal_environment=lambda **_kwargs: {
                    "HOME": str(home),
                    "CODEX_HOME": str(home / ".codex"),
                },
                run_confined_command=run_confined_command,
            )
            isolation = SimpleNamespace(
                SAFE_RUN_ID=re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$"),
                LEAN_EXPLORE_VERSION="fixture",
                _plain_directory=lambda path, **_kwargs: Path(path).resolve(strict=True),
                _plain_file=lambda path, **_kwargs: Path(path).resolve(strict=True),
                _validate_lean_explore_hf_cache=lambda _path: {"files": 1},
                _validate_controller_dir=lambda _path: None,
                _require_disjoint=lambda _paths: None,
                _install_seccomp_receive_deadline=lambda _sealed: None,
                _allow_seccomp_socketpair=lambda _sealed: None,
                _allow_seccomp_native_sockets=lambda _sealed: None,
                _parameterize_ipho_targets=lambda _sealed: None,
                _ensure_legacy_umbrella_anchor=lambda _workspace: "fixture",
                _project_lean_explore_cache=lambda _cache, _home: {"ok": True},
                _promote_dev_null_writable=lambda _sealed, value: value,
                _promote_dev_shm_writable=lambda _sealed, value: value,
                _extend_readonly_policy=lambda _sealed, value, *_args, **_kwargs: value,
                _lean_explore_hf_environment=lambda path: {"HF_HOME": str(path)},
                _sha256_file=lambda _path: "0" * 64,
                _write_new_json=lambda path, value: path.write_text(json.dumps(value)),
            )
            with (
                mock.patch.object(MODULE, "_load_sealed_helper", return_value=sealed),
                mock.patch.object(
                    MODULE,
                    "_validate_prepared_formalization_frontier",
                    return_value={
                        "target_count": 28,
                        "stage": "autoformalize",
                        "harness": "answer-blind-gpt",
                    },
                ),
                mock.patch.object(
                    MODULE,
                    "_copy_minimal_codex_auth",
                    side_effect=lambda _auth, target, _identity: target / ".codex",
                ),
            ):
                result, exit_code = MODULE.run(args, isolation=isolation)

            self.assertEqual(exit_code, 0)
            self.assertEqual(result["model"], "gpt-5.6-sol")
            self.assertEqual(calls["policy"]["allowed_connect_tcp_ports"], (443,))
            command = calls["command"]
            self.assertEqual(command["environment"]["CODEX_HOME"], str(home / ".codex"))
            self.assertFalse(
                any(
                    key.startswith(("OPENAI_", "ANTHROPIC_"))
                    for key in command["environment"]
                )
            )
            self.assertEqual(
                command["argv"][command["argv"].index("--max-parallel") + 1],
                "32",
            )


if __name__ == "__main__":
    unittest.main()
