from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import Any


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "configure_answer_blind_workspace.py"
)
SPEC = importlib.util.spec_from_file_location("answer_blind_workspace_config", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

SEED_SCRIPT = SCRIPT.with_name("build_answer_blind_solver_seed.py")
SEED_SPEC = importlib.util.spec_from_file_location(
    "answer_blind_seed_builder_for_config_tests", SEED_SCRIPT
)
assert SEED_SPEC and SEED_SPEC.loader
SEED_MODULE = importlib.util.module_from_spec(SEED_SPEC)
SEED_SPEC.loader.exec_module(SEED_MODULE)


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _strings(value: Any):
    if isinstance(value, dict):
        for key, child in value.items():
            yield str(key)
            yield from _strings(child)
    elif isinstance(value, list):
        for child in value:
            yield from _strings(child)
    elif isinstance(value, str):
        yield value


class AnswerBlindWorkspaceConfigTests(unittest.TestCase):
    def _workspace(self, parent: Path, name: str, *, git: bool = False) -> Path:
        root = parent / name
        controller = parent / f"{name}-controller"
        source = controller / "source"
        engine = source / "src/archon"
        (engine / ".archon-src/prompts").mkdir(parents=True)
        (source / "pyproject.toml").write_text(
            '[project]\nname="archon"\nversion="0.0.0"\n', encoding="utf-8"
        )
        (engine / "__init__.py").write_text("VERSION = 1\n", encoding="utf-8")
        (engine / ".archon-src/prompts/prove.md").write_text(
            "Derive only from the problem.\n", encoding="utf-8"
        )
        lake = source / "icho_2026_run"
        lake_files = {
            "lakefile.toml": 'name = "blind_test"\n',
            "lake-manifest.json": '{"version":"1.2.0","packages":[]}\n',
            "lean-toolchain": "leanprover/lean4:v4.31.0\n",
            "IChO2026Run/Basic.lean": "import Mathlib\n",
            "IChO2026Run/Dependencies.lean": "import Mathlib\n",
            "IChO2026Chem.lean": (
                "import IChO2026Chem.Core\nimport IChO2026Chem.Reporting\n"
            ),
            "IChO2026Chem/Core.lean": "import Mathlib\n",
            "IChO2026Chem/Reporting.lean": "import Mathlib\n",
        }
        for relative, text in lake_files.items():
            path = lake / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        images = controller / "images"
        images.mkdir(parents=True)
        image = images / "T1_page-1.png"
        image.write_bytes(b"problem image")
        pdf = controller / "theory_problem.pdf"
        pdf.write_bytes(b"problem pdf")
        bundle = controller / "questions_only.jsonl"
        bundle.write_text(
            json.dumps(
                {
                    "id": "icho_2026_t1_a1",
                    "evaluation_mode": "answer_blind",
                    "official_answer_seen": False,
                    "phase": "solve",
                    "current_question": "Derive the requested quantity.",
                    "images": ["T1_page-1.png"],
                    "source_pdf": "theory_problem.pdf",
                    "problem_assets": [
                        {
                            "kind": "problem_page",
                            "path": "T1_page-1.png",
                            "sha256": _sha256(image.read_bytes()),
                        },
                        {
                            "kind": "problem_pdf",
                            "path": "theory_problem.pdf",
                            "sha256": _sha256(pdf.read_bytes()),
                        },
                    ],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        SEED_MODULE.build_seed(
            source_root=source,
            lake_root=lake,
            questions_only=bundle,
            problem_pdf=pdf,
            image_root=images,
            problem_images=["T1_page-1.png"],
            output_dir=root,
            source_commit="a" * 40,
        )
        if git:
            subprocess.run(
                ["git", "init", "--quiet", "--initial-branch=main", "--template="],
                cwd=root,
                check=True,
            )
        return root

    def _read(self, root: Path):
        config = json.loads((root / ".archon/config.json").read_text(encoding="utf-8"))
        mcp = json.loads((root / ".mcp.json").read_text(encoding="utf-8"))
        protocol = (root / "ANSWER_BLIND_PROTOCOL.md").read_text(encoding="utf-8")
        return config, mcp, protocol

    def test_gpt_variant_pins_harness_and_common_review_schema(self):
        with tempfile.TemporaryDirectory() as raw:
            root = self._workspace(Path(raw), "gpt", git=True)
            manifest = MODULE.configure_answer_blind_workspace(
                root, variant="gpt", max_objectives=7, max_parallel=3
            )
            config, mcp, protocol = self._read(root)

            self.assertEqual(config["schema_version"], 1)
            self.assertEqual(config["answer_blind"]["authority"], "problem-only")
            self.assertFalse(config["answer_blind"]["official_answer_seen"])
            self.assertEqual(
                config["answer_blind"]["isolation"],
                {
                    "filesystem_answer_blind": True,
                    "network_answer_blind": False,
                },
            )
            loop = config["loop"]
            self.assertEqual(loop["domain_profile"]["name"], "chemistry")
            self.assertEqual(loop["max_objectives"], 7)
            self.assertEqual(loop["max_parallel"], 3)
            for enabled in (
                "formalization_review_gate",
                "proof_review_gate",
                "axiom_sweep",
                "deterministic_plan",
                "deterministic_review",
                "parallel_target_review",
                "parallel_formalization_review",
            ):
                self.assertTrue(loop[enabled], enabled)
            self.assertFalse(loop["pipeline_target_review"])
            self.assertEqual(config["subagents"], {"enabled": []})
            self.assertEqual(config["multilane"], {"enabled": False, "lanes": []})

            descriptor = config["harnesses"][loop["harness"]]
            self.assertEqual(descriptor["runner"], "codex")
            self.assertEqual(descriptor["model"], "gpt-5.6-sol")
            self.assertEqual(descriptor["effort"], "max")
            self.assertEqual(descriptor["sandbox"], "workspace-write")
            self.assertIs(descriptor["ignore_user_config"], True)
            self.assertEqual(
                descriptor["base_url_env"], "ANSWER_BLIND_MODEL_BASE_URL"
            )
            self.assertEqual(
                descriptor["key_env"], "ANSWER_BLIND_MODEL_DUMMY_KEY"
            )
            self.assertEqual(descriptor["wire_api"], "responses")
            self.assertEqual(
                descriptor["lean_lsp_mcp_bin"], "lean-lsp-mcp-trusted"
            )
            self.assertEqual(descriptor["mcp"], ["lean-lsp"])
            flags = " ".join(descriptor["extra_args"])
            for disabled in ("plugins", "browser", "web_search", "search", "websockets"):
                self.assertIn(disabled, flags)

            self.assertEqual(set(mcp["mcpServers"]), {"lean-lsp"})
            self.assertEqual(mcp["mcpServers"]["lean-lsp"]["type"], "stdio")
            self.assertEqual(
                mcp["mcpServers"]["lean-lsp"]["command"],
                "lean-lsp-mcp-trusted",
            )
            self.assertEqual(mcp["mcpServers"]["lean-lsp"]["args"], [])
            self.assertIn("problem-only", protocol)
            self.assertIn("filesystem_answer_blind = true", protocol)
            agents = (root / ".archon/AGENTS.md").read_text(encoding="utf-8")
            self.assertIn("Never search the web", agents)
            self.assertIn("ANSWER_BLIND_PROTOCOL.md", agents)
            self.assertNotIn("WebSearch", agents)
            self.assertEqual(
                manifest["isolation"],
                {
                    "filesystem_answer_blind": True,
                    "network_answer_blind": False,
                },
            )

    def test_kimi_variant_is_bare_strict_and_has_no_provider_credentials(self):
        with tempfile.TemporaryDirectory() as raw:
            root = self._workspace(Path(raw), "k3")
            MODULE.configure_workspace(
                root, variant="kimi-k3", max_objectives=11, max_parallel=4
            )
            config, mcp, _protocol = self._read(root)
            descriptor = config["harnesses"][config["loop"]["harness"]]
            self.assertEqual(descriptor["runner"], "claude-code")
            self.assertEqual(descriptor["model"], "kimi-k3[1m]")
            self.assertEqual(
                descriptor["claude_extra_args"],
                [
                    "--bare",
                    "--no-session-persistence",
                    "--effort",
                    "max",
                    "--strict-mcp-config",
                    "--mcp-config",
                    ".mcp.json",
                ],
            )
            self.assertTrue(
                {"Bash", "WebSearch", "WebFetch", "Agent", "Task", "ScheduleWakeup"}
                <= set(descriptor["disallowed_tools"])
            )
            serialized = json.dumps(descriptor, sort_keys=True).casefold()
            for forbidden in ("token", "api_key", "base_url", "password", "secret"):
                self.assertNotIn(forbidden, serialized)
            self.assertEqual(set(mcp["mcpServers"]), {"lean-lsp"})

    def test_optional_lean_explore_is_loopback_only(self):
        with tempfile.TemporaryDirectory() as raw:
            parent = Path(raw)
            root = self._workspace(parent, "loopback")
            url = "http://127.0.0.1:8765/mcp"
            MODULE.configure_workspace(
                root,
                variant="gpt",
                max_objectives=2,
                max_parallel=1,
                lean_explore_url=url,
            )
            config, mcp, _protocol = self._read(root)
            self.assertEqual(set(mcp["mcpServers"]), {"lean-lsp", "lean-explore"})
            self.assertEqual(mcp["mcpServers"]["lean-explore"], {"type": "http", "url": url})
            descriptor = config["harnesses"][config["loop"]["harness"]]
            self.assertEqual(descriptor["mcp"], ["lean-lsp", "lean-explore"])
            self.assertEqual(descriptor["lean_explore_url"], url)

            remote = self._workspace(parent, "remote")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "loopback"):
                MODULE.configure_workspace(
                    remote,
                    variant="kimi-k3",
                    lean_explore_url="https://example.test/mcp",
                )
            self.assertFalse((remote / ".mcp.json").exists())

    def test_generated_files_are_path_safe_credential_free_and_deterministic(self):
        with tempfile.TemporaryDirectory() as raw:
            parent = Path(raw)
            first = self._workspace(parent, "model-one")
            second = self._workspace(parent, "model-two")
            first_manifest = MODULE.configure_workspace(
                first, variant="kimi-k3", max_objectives=5, max_parallel=2
            )
            second_manifest = MODULE.configure_workspace(
                second, variant="kimi-k3", max_objectives=5, max_parallel=2
            )
            self.assertEqual(first_manifest, second_manifest)
            for relative in MODULE.GENERATED_FILES:
                self.assertEqual((first / relative).read_bytes(), (second / relative).read_bytes())

            config, mcp, protocol = self._read(first)
            generated_text = "\n".join(
                [json.dumps(config, sort_keys=True), json.dumps(mcp, sort_keys=True), protocol]
            )
            self.assertNotIn(str(first), generated_text)
            self.assertNotIn(str(second), generated_text)
            self.assertNotIn("/root", generated_text.casefold())
            self.assertNotIn("model-two", generated_text)
            for value in [*_strings(config), *_strings(mcp)]:
                if value.startswith("http://"):
                    continue
                self.assertFalse(value.startswith("/"), value)
                self.assertFalse(len(value) > 2 and value[1:3] in (":\\", ":/"), value)

            # Reapplying the same request is byte-for-byte idempotent.
            before = {name: (first / name).read_bytes() for name in MODULE.GENERATED_FILES}
            again = MODULE.configure_workspace(
                first, variant="kimi-k3", max_objectives=5, max_parallel=2
            )
            self.assertEqual(first_manifest, again)
            self.assertEqual(
                before,
                {name: (first / name).read_bytes() for name in MODULE.GENERATED_FILES},
            )

    def test_rejects_remote_history_tampering_and_unsanitized_files(self):
        with tempfile.TemporaryDirectory() as raw:
            parent = Path(raw)
            remote = self._workspace(parent, "has-remote", git=True)
            subprocess.run(
                ["git", "remote", "add", "origin", "https://example.test/repo.git"],
                cwd=remote,
                check=True,
            )
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "remotes"):
                MODULE.configure_workspace(remote, variant="gpt")

            dirty = self._workspace(parent, "extra-file")
            (dirty / "prior-model-report.md").write_text("prior result\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "outside"):
                MODULE.configure_workspace(dirty, variant="gpt")

            changed = self._workspace(parent, "changed")
            bundle = changed / "icho_2026_source/questions_only.jsonl"
            bundle.write_text("tampered\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "hash mismatch"):
                MODULE.configure_workspace(changed, variant="gpt")

    def test_rejects_missing_manifest_invalid_limits_and_output_symlinks(self):
        with tempfile.TemporaryDirectory() as raw:
            parent = Path(raw)
            missing = parent / "missing"
            missing.mkdir()
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "manifest"):
                MODULE.configure_workspace(missing, variant="gpt")

            invalid = self._workspace(parent, "invalid")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "positive"):
                MODULE.configure_workspace(invalid, variant="gpt", max_parallel=0)

            linked = self._workspace(parent, "linked")
            outside = parent / "outside.json"
            outside.write_text("unchanged\n", encoding="utf-8")
            try:
                (linked / ".mcp.json").symlink_to(outside)
            except OSError as exc:  # pragma: no cover - platform limitation
                self.skipTest(f"symbolic links unavailable: {exc}")
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "symbolic link|unsafe"):
                MODULE.configure_workspace(linked, variant="gpt")
            self.assertEqual(outside.read_text(encoding="utf-8"), "unchanged\n")

    def test_rejects_self_authored_minimal_manifest_even_when_hashes_match(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "forged"
            bundle = root / "icho_2026_source/questions_only.jsonl"
            bundle.parent.mkdir(parents=True)
            bundle.write_text(
                '{"id":"icho_2026_t1_a1","evaluation_mode":"answer_blind",'
                '"official_answer_seen":false,"phase":"solve"}\n',
                encoding="utf-8",
            )
            relative = bundle.relative_to(root).as_posix()
            (root / MODULE.SEED_MANIFEST).write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "protocol": MODULE.SEED_PROTOCOL,
                        "isolation_claims": {"filesystem": True, "network": False},
                        "workspace_policy": {
                            "fresh_git_init": True,
                            "history": False,
                            "remotes": [],
                            "solver_labels": ["GPT", "K3"],
                        },
                        "payload_files": {relative: _sha256(bundle.read_bytes())},
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(MODULE.WorkspaceConfigError, "full seed validation"):
                MODULE.configure_workspace(root, variant="gpt")


if __name__ == "__main__":
    unittest.main()
