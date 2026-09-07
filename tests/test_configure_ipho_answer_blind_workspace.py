from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "configure_ipho_answer_blind_workspace.py"
)
SPEC = importlib.util.spec_from_file_location("ipho_workspace_config", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IphoAnswerBlindWorkspaceConfigTests(unittest.TestCase):
    def _workspace(self, root: Path) -> Path:
        workspace = root / "solver"
        payload = {
            "lean-toolchain": b"leanprover/lean4:v4.31.0\n",
            "lakefile.toml": b'name = "IPhO2026Run"\n',
            "questions-only.jsonl": (
                b'{"evaluation_mode":"answer_blind",'
                b'"official_answer_seen":false,"question":"derive it"}\n'
            ),
            "IPhO2026Problems/problem_sample.lean": b"import Mathlib\nimport Physlib\n",
        }
        for relative, contents in payload.items():
            path = workspace / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents)
        manifest = {
            "schema_version": 1,
            "protocol": MODULE.SEED_PROTOCOL,
            "isolation": {
                "filesystem_answer_blind": True,
                "network_answer_blind": False,
            },
            "workspace_policy": {
                "fresh_git_init": True,
                "history": False,
                "remotes": [],
            },
            "payload_files": {
                relative: hashlib.sha256(contents).hexdigest()
                for relative, contents in payload.items()
            },
        }
        (workspace / MODULE.SEED_MANIFEST).write_text(
            json.dumps(manifest), encoding="utf-8"
        )
        return workspace

    @staticmethod
    def _git(workspace: Path, *arguments: str) -> None:
        subprocess.run(
            ["git", *arguments],
            cwd=workspace,
            check=True,
            capture_output=True,
            text=True,
        )

    def test_generates_pinned_physics_configuration(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = self._workspace(Path(raw))
            receipt = MODULE.configure_workspace(
                workspace,
                variant="kimi-k3",
                max_objectives=28,
                max_parallel=4,
                lean_explore_url="http://127.0.0.1:18765/mcp",
            )

            config = json.loads(
                (workspace / ".archon/config.json").read_text(encoding="utf-8")
            )
            loop = config["loop"]
            descriptor = config["harnesses"][loop["harness"]]
            profile = loop["domain_profile"]
            self.assertEqual(config["answer_blind"]["protocol"], MODULE.PROTOCOL)
            self.assertEqual(config["answer_blind"]["authority"], "problem-only")
            self.assertFalse(config["answer_blind"]["official_answer_seen"])
            self.assertEqual(loop["model"], "anthropic-kimi-k3")
            self.assertEqual(loop["max_objectives"], 28)
            self.assertEqual(loop["max_parallel"], 4)
            self.assertTrue(loop["physics_aware"])
            self.assertTrue(loop["parallel_formalization_review"])
            self.assertTrue(loop["parallel_target_review"])
            self.assertTrue(loop["pipeline_target_review"])
            self.assertEqual(profile["name"], "physics")
            self.assertEqual(profile["preflight_imports"], ["Mathlib", "Physlib"])
            self.assertEqual(
                profile["lean_search_packages"], ["Mathlib", "Physlib"]
            )
            self.assertEqual(profile["target_import_prefixes"], ["Physlib"])
            self.assertEqual(descriptor["runner"], "claude-code")
            self.assertEqual(descriptor["model"], "anthropic-kimi-k3")
            self.assertEqual(descriptor["lean_explore_backend"], "local")
            self.assertNotIn("ToolSearch", descriptor["disallowed_tools"])
            self.assertTrue(
                {
                    "ListMcpResourcesTool",
                    "ReadMcpResourceDirTool",
                    "ReadMcpResourceTool",
                }.issubset(descriptor["disallowed_tools"])
            )
            prompt_index = descriptor["claude_extra_args"].index(
                "--append-system-prompt"
            )
            self.assertEqual(
                descriptor["claude_extra_args"][prompt_index + 1],
                MODULE.KIMI_PDF_COMPATIBILITY_PROMPT,
            )
            self.assertIn("never /tmp", MODULE.KIMI_PDF_COMPATIBILITY_PROMPT)
            self.assertIn(
                "rerank_top: 0",
                MODULE.KIMI_PDF_COMPATIBILITY_PROMPT,
            )
            self.assertIn(
                "lake env lean",
                MODULE.KIMI_PDF_COMPATIBILITY_PROMPT,
            )
            self.assertIn(
                "never hard-code an absolute lake path",
                MODULE.KIMI_PDF_COMPATIBILITY_PROMPT,
            )
            self.assertEqual(
                descriptor["lean_explore_url"], "http://127.0.0.1:18765/mcp"
            )

            mcp = json.loads((workspace / ".mcp.json").read_text(encoding="utf-8"))
            self.assertEqual(set(mcp["mcpServers"]), {"lean-explore"})
            self.assertEqual(
                mcp["mcpServers"]["lean-explore"]["url"],
                "http://127.0.0.1:18765/mcp",
            )

            generated = "\n".join(
                (workspace / relative).read_text(encoding="utf-8")
                for relative in MODULE.GENERATED_FILES
            ).casefold()
            self.assertNotIn("chemistry", generated)
            self.assertNotIn("crnt", generated)
            self.assertNotIn("/root", generated)
            self.assertNotIn("api_key", generated)
            self.assertNotIn("auth_token", generated)
            self.assertNotIn("base_url", generated)
            self.assertIn("never use", generated)
            self.assertIn("`read`", generated)
            self.assertIn("`.pdf`", generated)
            self.assertIn("problem-page png", generated)

            for relative, metadata in receipt["files"].items():
                contents = (workspace / relative).read_bytes()
                self.assertEqual(metadata["sha256"], hashlib.sha256(contents).hexdigest())
                self.assertEqual(metadata["size"], len(contents))

    def test_local_grounding_without_mcp_url(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = self._workspace(Path(raw))
            MODULE.configure_workspace(workspace, variant="kimi-k3")
            config = json.loads(
                (workspace / ".archon/config.json").read_text(encoding="utf-8")
            )
            loop = config["loop"]
            descriptor = config["harnesses"][loop["harness"]]
            self.assertEqual(descriptor["lean_explore_backend"], "local")
            self.assertNotIn("lean_explore_url", descriptor)
            mcp = json.loads((workspace / ".mcp.json").read_text(encoding="utf-8"))
            self.assertEqual(set(mcp["mcpServers"]), {"lean-explore"})
            self.assertEqual(
                mcp["mcpServers"]["lean-explore"],
                {
                    "type": "stdio",
                    "command": "python",
                    "env": {
                        "OMP_NUM_THREADS": "1",
                        "OPENBLAS_NUM_THREADS": "1",
                        "RAYON_NUM_THREADS": "1",
                    },
                    "args": [
                        "-P",
                        "-m",
                        "archon.commands.tooling.lean_explore_mcp_shim",
                        "--backend",
                        "local",
                        "--transport",
                        "stdio",
                    ],
                    "timeout": 600000,
                },
            )

    def test_gpt_variant_is_ephemeral_and_has_only_physics_grounding(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = self._workspace(Path(raw))
            MODULE.configure_workspace(
                workspace,
                variant="gpt",
                max_objectives=28,
                max_parallel=32,
            )
            config = json.loads(
                (workspace / ".archon/config.json").read_text(encoding="utf-8")
            )
            loop = config["loop"]
            descriptor = config["harnesses"][loop["harness"]]

            self.assertEqual(loop["model"], "gpt-5.6-sol")
            self.assertEqual(loop["max_objectives"], 28)
            self.assertEqual(loop["max_parallel"], 32)
            self.assertEqual(loop["domain_profile"]["name"], "physics")
            self.assertEqual(
                loop["domain_profile"]["lean_search_packages"],
                ["Mathlib", "Physlib"],
            )
            self.assertEqual(descriptor["runner"], "codex")
            self.assertEqual(descriptor["model"], "gpt-5.6-sol")
            self.assertEqual(descriptor["effort"], "max")
            self.assertTrue(descriptor["ephemeral"])
            self.assertTrue(descriptor["ignore_user_config"])
            self.assertEqual(descriptor["mcp"], ["lean-explore"])
            self.assertEqual(descriptor["lean_explore_backend"], "local")
            self.assertNotIn("base_url_env", descriptor)
            self.assertNotIn("key_env", descriptor)
            self.assertNotIn("codex_home", descriptor)
            for disabled in (
                "features.plugins=false",
                "features.apps=false",
                "features.browser_use=false",
                "features.multi_agent=false",
                'web_search="disabled"',
            ):
                self.assertIn(disabled, descriptor["extra_args"])

            mcp = json.loads((workspace / ".mcp.json").read_text(encoding="utf-8"))
            self.assertEqual(set(mcp["mcpServers"]), {"lean-explore"})
            generated = "\n".join(
                (workspace / relative).read_text(encoding="utf-8")
                for relative in MODULE.GENERATED_FILES
            ).casefold()
            self.assertIn("gpt-5.6-sol", generated)
            self.assertNotIn("kimi compatibility", generated)
            self.assertNotIn("claude code", generated)

    def test_payload_tampering_and_unlisted_files_fail_closed(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = self._workspace(Path(raw))
            (workspace / "questions-only.jsonl").write_text("changed\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "hash mismatch"):
                MODULE.configure_workspace(workspace, variant="kimi-k3")
            self.assertFalse((workspace / ".archon/config.json").exists())

        with tempfile.TemporaryDirectory() as raw:
            workspace = self._workspace(Path(raw))
            (workspace / "unsealed.txt").write_text("extra", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "outside.*inventory"):
                MODULE.configure_workspace(workspace, variant="kimi-k3")
            self.assertFalse((workspace / ".archon/config.json").exists())

    def test_fresh_git_is_allowed_but_remote_or_history_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            workspace = self._workspace(Path(raw))
            self._git(workspace, "init", "--quiet")
            MODULE.validate_solver_workspace(workspace)
            self._git(workspace, "remote", "add", "origin", "https://invalid.example/repo")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "must not have Git remotes"):
                MODULE.validate_solver_workspace(workspace)

        with tempfile.TemporaryDirectory() as raw:
            workspace = self._workspace(Path(raw))
            self._git(workspace, "init", "--quiet")
            self._git(workspace, "add", ".")
            self._git(
                workspace,
                "-c",
                "user.name=fixture",
                "-c",
                "user.email=fixture@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "history must be rejected",
            )
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "history must be empty"):
                MODULE.validate_solver_workspace(workspace)

    def test_only_explicit_loopback_lean_explore_url_is_allowed(self):
        for value in (
            "https://127.0.0.1:8765/mcp",
            "http://example.com:8765/mcp",
            "http://127.0.0.1/mcp",
            "http://user:pass@127.0.0.1:8765/mcp",
            "http://127.0.0.1:8765/mcp?query=1",
        ):
            with self.subTest(value=value):
                with self.assertRaises(MODULE.WorkspaceConfigError):
                    MODULE.build_mcp_config(lean_explore_url=value)
        self.assertEqual(
            MODULE.build_mcp_config(
                lean_explore_url="http://localhost:8765/mcp"
            )["mcpServers"]["lean-explore"]["url"],
            "http://localhost:8765/mcp",
        )

    def test_variant_and_parallelism_are_fail_closed(self):
        with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "variant"):
            MODULE.build_archon_config(variant="unsupported")
        for field, kwargs in (
            ("max_objectives", {"max_objectives": 0}),
            ("max_parallel", {"max_parallel": True}),
        ):
            with self.subTest(field=field):
                with self.assertRaisesRegex(MODULE.WorkspaceConfigError, field):
                    MODULE.build_archon_config(variant="kimi-k3", **kwargs)


if __name__ == "__main__":
    unittest.main()
