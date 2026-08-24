from __future__ import annotations

import hashlib
import importlib.util
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/install_answer_blind_runtime_wrappers.py"
CAMPAIGN_SOURCE = ROOT / "scripts/run_answer_blind_gpt_campaign.py"
ISOLATED_SOURCE = ROOT / "scripts/run_answer_blind_archon_isolated_campaign.py"
AXIOM_CHECKER_SOURCE = (
    ROOT
    / "src/archon/.archon-src/skills/lean4/lib/scripts/check_axioms_inline.sh"
)
SPEC = importlib.util.spec_from_file_location("answer_blind_runtime_installer", SCRIPT)
assert SPEC and SPEC.loader
INSTALLER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = INSTALLER
SPEC.loader.exec_module(INSTALLER)


@unittest.skipUnless(os.geteuid() == 0, "runtime installation is root-only")
class AnswerBlindRuntimeInstallerTests(unittest.TestCase):
    def _standalone_release(
        self, base: Path, *, include_host: bool = True,
        release: str = "0.147.0-x86_64-unknown-linux-musl",
        binary_version: str = "0.147.0",
    ) -> tuple[Path, Path, Path]:
        release_bin = base / "standalone/releases" / release / "bin"
        release_bin.mkdir(parents=True)
        codex = release_bin / "codex"
        codex.write_text(
            "#!/bin/sh\nprintf 'codex-cli %s\\n'\n" % binary_version,
            encoding="utf-8",
        )
        codex.chmod(0o755)
        host = release_bin / "codex-code-mode-host"
        if include_host:
            host.write_bytes(b"exact-host-release-payload\x00\xff")
            host.chmod(0o755)
        launcher = base / "launcher/codex"
        launcher.parent.mkdir(parents=True)
        launcher.symlink_to(codex)
        return launcher, codex, host

    def _which(self, base: Path, launcher: Path):
        generic = base / "generic-tool"
        generic.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        generic.chmod(0o755)

        def resolve(name: str) -> str:
            return str(launcher if name == "codex" else generic)

        return resolve

    def _which_with_real_host_tools(self, launcher: Path):
        host_which = shutil.which

        def resolve(name: str) -> str | None:
            return str(launcher) if name == "codex" else host_which(name)

        return resolve

    def _run_axiom_checker_fixture(
        self,
        output: str,
        *,
        report_only: bool,
    ) -> subprocess.CompletedProcess[str]:
        host_bash = shutil.which("bash")
        if host_bash is None:
            self.skipTest("bash is unavailable for the axiom-checker fixture")

        with tempfile.TemporaryDirectory(prefix="answer-blind-axiom-fixture-") as raw:
            base = Path(raw)
            fake_bin = base / "bin"
            fake_bin.mkdir()
            fake_lake = fake_bin / "lake"
            fake_lake.write_text(
                "#!/bin/sh\n"
                "printf '%s' \"${AXIOM_FIXTURE_OUTPUT-}\"\n",
                encoding="utf-8",
            )
            fake_lake.chmod(0o755)

            project = base / "project"
            project.mkdir()
            source = project / "Fixture.lean"
            original = "theorem fixtureDecl : True := by\n  trivial\n"
            source.write_text(original, encoding="utf-8")
            environment = os.environ.copy()
            environment["PATH"] = os.pathsep.join(
                (str(fake_bin), environment.get("PATH", ""))
            )
            environment["AXIOM_FIXTURE_OUTPUT"] = output
            command = [
                host_bash,
                str(AXIOM_CHECKER_SOURCE),
                str(source),
                "--verbose",
            ]
            if report_only:
                command.append("--report-only")

            result = subprocess.run(
                command,
                cwd=project,
                check=False,
                capture_output=True,
                text=True,
                env=environment,
                timeout=10,
            )

            self.assertEqual(source.read_text(encoding="utf-8"), original)
            self.assertFalse(source.with_suffix(".lean.axiom_check_backup").exists())
            return result

    def test_controller_tools_fail_closed_when_standalone_host_is_missing(self) -> None:
        with tempfile.TemporaryDirectory(prefix="answer-blind-codex-pair-") as raw:
            base = Path(raw)
            launcher, _codex, host = self._standalone_release(
                base, include_host=False
            )
            runtime = base / "runtime"
            with mock.patch.object(
                INSTALLER.shutil, "which", side_effect=self._which(base, launcher)
            ):
                with self.assertRaisesRegex(FileNotFoundError, "missing sibling host"):
                    INSTALLER._copy_controller_tools(runtime)
            self.assertFalse(host.exists())
            self.assertFalse((runtime / "bin").exists())

    def test_controller_tools_copy_exact_standalone_pair_root_owned_0555(self) -> None:
        with tempfile.TemporaryDirectory(prefix="answer-blind-codex-pair-") as raw:
            base = Path(raw)
            launcher, codex, host = self._standalone_release(base)
            runtime = base / "runtime"
            expected = {
                "codex": hashlib.sha256(codex.read_bytes()).hexdigest(),
                "codex-code-mode-host": hashlib.sha256(host.read_bytes()).hexdigest(),
            }
            with mock.patch.object(
                INSTALLER.shutil, "which", side_effect=self._which(base, launcher)
            ):
                INSTALLER._copy_controller_tools(runtime)

            for name, expected_sha in expected.items():
                installed = runtime / "bin" / name
                self.assertEqual(
                    hashlib.sha256(installed.read_bytes()).hexdigest(), expected_sha
                )
                self.assertEqual(installed.stat().st_uid, 0)
                self.assertEqual(stat.S_IMODE(installed.stat().st_mode), 0o555)

    def test_axiom_checker_tools_are_exact_root_owned_0555_files(self) -> None:
        with tempfile.TemporaryDirectory(prefix="answer-blind-axiom-tools-") as raw:
            base = Path(raw)
            launcher, _codex, _host = self._standalone_release(base)
            runtime = base / "runtime"
            expected = {
                name: hashlib.sha256(
                    INSTALLER._resolve_trusted_system_executable(name).read_bytes()
                ).hexdigest()
                for name in INSTALLER.AXIOM_CHECKER_SYSTEM_TOOLS
            }

            with mock.patch.object(
                INSTALLER.shutil, "which", side_effect=self._which(base, launcher)
            ):
                INSTALLER._copy_controller_tools(runtime)

            self.assertEqual(
                tuple(expected),
                (
                    "mktemp", "awk", "cat", "mv", "rm", "find", "realpath",
                    "dirname", "basename", "sort", "cp", "grep", "head",
                    "cut", "sed",
                ),
            )
            for name, expected_sha in expected.items():
                with self.subTest(tool=name):
                    installed = runtime / "bin" / name
                    metadata = installed.stat(follow_symlinks=False)
                    self.assertTrue(stat.S_ISREG(metadata.st_mode))
                    self.assertFalse(installed.is_symlink())
                    self.assertEqual(metadata.st_uid, 0)
                    self.assertEqual(stat.S_IMODE(metadata.st_mode), 0o555)
                    self.assertEqual(
                        hashlib.sha256(installed.read_bytes()).hexdigest(),
                        expected_sha,
                    )

    def test_axiom_checker_runs_real_lean_with_runtime_only_system_tools(self) -> None:
        host_lean = shutil.which("lean")
        if host_lean is None:
            self.skipTest("Lean is unavailable for the axiom-checker smoke test")
        prefix_probe = subprocess.run(
            [host_lean, "--print-prefix"],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
        if prefix_probe.returncode != 0:
            self.skipTest("Lean prefix probe failed")
        lean_bin = Path(prefix_probe.stdout.strip()) / "bin"
        if not (lean_bin / "lake").is_file() or not (lean_bin / "lean").is_file():
            self.skipTest("Lean toolchain has no direct lake/lean pair")

        with tempfile.TemporaryDirectory(prefix="answer-blind-axiom-smoke-") as raw:
            base = Path(raw)
            launcher, _codex, _host = self._standalone_release(base)
            runtime = base / "runtime"
            with mock.patch.object(
                INSTALLER.shutil,
                "which",
                side_effect=self._which_with_real_host_tools(launcher),
            ):
                INSTALLER._copy_controller_tools(runtime)

            project = base / "project"
            project.mkdir()
            source = project / "AxiomSmoke.lean"
            original = (
                "import Std.Tactic\n\n"
                "axiom propextTrap : True\n\n"
                "axiom extraordinarilyLongCustomAxiomAlpha : True\n"
                "axiom extraordinarilyLongCustomAxiomBeta : True\n"
                "axiom extraordinarilyLongCustomAxiomGamma : True\n"
                "axiom extraordinarilyLongCustomAxiomDelta : True\n\n"
                "theorem smoke : True := by\n"
                "  trivial\n\n"
                "noncomputable section\n\n"
                "def standardSmoke {α : Type} (h : Nonempty α) "
                "{p q : Prop} (hpq : p ↔ q) : { _a : α // p = q } :=\n"
                "  ⟨Classical.choice h, propext hpq⟩\n\n"
                "theorem customSmoke : True := propextTrap\n\n"
                "theorem wrappedSmoke : True ∧ True ∧ True ∧ True :=\n"
                "  ⟨extraordinarilyLongCustomAxiomAlpha, "
                "extraordinarilyLongCustomAxiomBeta, "
                "extraordinarilyLongCustomAxiomGamma, "
                "extraordinarilyLongCustomAxiomDelta⟩\n\n"
                "theorem nativeSmoke : (37 : Nat) = 37 := by\n"
                "  native_decide\n"
            )
            source.write_text(original, encoding="utf-8")
            (project / "lakefile.toml").write_text(
                'name = "AxiomSmoke"\n'
                'version = "0.1.0"\n'
                'defaultTargets = ["AxiomSmoke"]\n\n'
                '[[lean_lib]]\n'
                'name = "AxiomSmoke"\n',
                encoding="utf-8",
            )
            home = base / "home"
            temporary = base / "tmp"
            home.mkdir()
            temporary.mkdir()
            runtime_bin = runtime / "bin"
            restricted_path = os.pathsep.join((str(runtime_bin), str(lean_bin)))
            environment = {
                "HOME": str(home),
                "TMPDIR": str(temporary),
                "TMP": str(temporary),
                "TEMP": str(temporary),
                "PATH": restricted_path,
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
            }
            self.assertNotIn("/usr/bin", restricted_path.split(os.pathsep))
            self.assertNotIn("/bin", restricted_path.split(os.pathsep))

            path_probe = subprocess.run(
                [
                    str(runtime_bin / "bash"),
                    "-c",
                    """
set -euo pipefail
runtime_bin=$1
shift
for name in "$@"; do
    resolved=$(type -P "$name")
    [[ "$resolved" == "$runtime_bin/$name" ]]
done
""",
                    "axiom-tool-path-probe",
                    str(runtime_bin),
                    *INSTALLER.AXIOM_CHECKER_SYSTEM_TOOLS,
                ],
                check=False,
                capture_output=True,
                text=True,
                env=environment,
                timeout=10,
            )
            self.assertEqual(
                path_probe.returncode,
                0,
                msg=f"stdout:\n{path_probe.stdout}\nstderr:\n{path_probe.stderr}",
            )

            result = subprocess.run(
                [
                    str(runtime_bin / "bash"),
                    str(AXIOM_CHECKER_SOURCE),
                    str(project),
                    "--verbose",
                    "--report-only",
                ],
                cwd=project,
                check=False,
                capture_output=True,
                text=True,
                env=environment,
                timeout=30,
            )
            self.assertEqual(
                result.returncode,
                0,
                msg=f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
            )
            self.assertIn("Files checked: 1", result.stdout)
            self.assertIn("Declarations checked: 5", result.stdout)
            self.assertIn(
                "customSmoke uses non-standard axiom: propextTrap",
                result.stdout,
            )
            self.assertIn(
                "nativeSmoke uses non-standard axiom: Lean.ofReduceBool",
                result.stdout,
            )
            self.assertIn(
                "nativeSmoke uses non-standard axiom: Lean.trustCompiler",
                result.stdout,
            )
            self.assertNotIn(
                "standardSmoke uses non-standard axiom",
                result.stdout,
            )
            for axiom in (
                "extraordinarilyLongCustomAxiomAlpha",
                "extraordinarilyLongCustomAxiomBeta",
                "extraordinarilyLongCustomAxiomGamma",
                "extraordinarilyLongCustomAxiomDelta",
            ):
                with self.subTest(wrapped_axiom=axiom):
                    self.assertIn(
                        f"wrappedSmoke uses non-standard axiom: {axiom}",
                        result.stdout,
                    )
            self.assertIn("Files with non-standard axioms: 1", result.stdout)
            self.assertIn("Total non-standard axiom usages: 7", result.stdout)
            self.assertEqual(source.read_text(encoding="utf-8"), original)
            self.assertFalse(source.with_suffix(".lean.axiom_check_backup").exists())

    def test_axiom_checker_parses_multiline_lean_431_fixture(self) -> None:
        result = self._run_axiom_checker_fixture(
            "'fixtureDecl' depends on axioms: [propext,\n"
            " Classical.choice,\n"
            " Custom.ax]\n",
            report_only=True,
        )

        self.assertEqual(
            result.returncode,
            0,
            msg=f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
        )
        self.assertIn(
            "fixtureDecl uses non-standard axiom: Custom.ax",
            result.stdout,
        )
        self.assertNotIn(
            "fixtureDecl uses non-standard axiom: propext",
            result.stdout,
        )
        self.assertNotIn(
            "fixtureDecl uses non-standard axiom: Classical.choice",
            result.stdout,
        )
        self.assertIn("Total non-standard axiom usages: 1", result.stdout)

    def test_axiom_checker_fails_closed_on_unrecognized_output(self) -> None:
        result = self._run_axiom_checker_fixture(
            "Lean axiom output format drifted\n",
            report_only=False,
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "Error: no recognizable #print axioms results",
            result.stderr,
        )
        self.assertIn("Files with errors: 1", result.stdout)
        self.assertNotIn("All files use only standard axioms", result.stdout)

    def test_axiom_checker_fails_closed_on_unterminated_bracket_list(self) -> None:
        result = self._run_axiom_checker_fixture(
            "'fixtureDecl' depends on axioms: [propext,\n"
            " Classical.choice,\n",
            report_only=False,
        )

        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "Error: unterminated #print axioms bracket list",
            result.stderr,
        )
        self.assertIn("Files with errors: 1", result.stdout)
        self.assertNotIn("All files use only standard axioms", result.stdout)

    def test_controller_tools_reject_codex_release_version_mismatch(self) -> None:
        with tempfile.TemporaryDirectory(prefix="answer-blind-codex-pair-") as raw:
            base = Path(raw)
            launcher, _codex, _host = self._standalone_release(
                base, release="0.146.0-x86_64-unknown-linux-musl"
            )
            runtime = base / "runtime"
            with mock.patch.object(
                INSTALLER.shutil, "which", side_effect=self._which(base, launcher)
            ):
                with self.assertRaisesRegex(RuntimeError, "does not match release"):
                    INSTALLER._copy_controller_tools(runtime)
            self.assertFalse((runtime / "bin").exists())

    def test_campaign_controller_and_wrapper_are_runtime_inventory_files(self) -> None:
        with tempfile.TemporaryDirectory(prefix="answer-blind-runtime-install-") as raw:
            runtime = Path(raw) / "runtime"
            python = runtime / "venv/bin/python"
            python.parent.mkdir(parents=True)
            python.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            python.chmod(0o755)
            module_root = (
                runtime
                / "venv/lib/python3.14/site-packages/archon/.archon-src/tools"
                / "lean-lsp-mcp/src/lean_lsp_mcp"
            )
            module_root.mkdir(parents=True)
            (module_root / "__main__.py").write_text("", encoding="utf-8")
            for relative in (
                ".pytest_cache/state",
                "venv/.mypy_cache/state",
                "venv/.ruff_cache/state",
                "venv/lib/python3.14/site-packages/pkg/__pycache__/module.pyc",
            ):
                cache_file = runtime / relative
                cache_file.parent.mkdir(parents=True, exist_ok=True)
                cache_file.write_bytes(b"generated-cache")

            with mock.patch.object(INSTALLER, "_copy_controller_tools"):
                INSTALLER.install(runtime_root=runtime, materialize_python=False)

            module = runtime / "libexec/run_answer_blind_gpt_campaign.py"
            wrapper = runtime / "bin/answer-blind-gpt-campaign"
            self.assertEqual(module.read_bytes(), CAMPAIGN_SOURCE.read_bytes())
            self.assertEqual(stat.S_IMODE(module.stat().st_mode), 0o444)
            self.assertEqual(module.stat().st_uid, 0)
            self.assertEqual(stat.S_IMODE(wrapper.stat().st_mode), 0o755)
            self.assertEqual(wrapper.stat().st_uid, 0)
            payload = wrapper.read_text(encoding="utf-8")
            self.assertIn(f"exec '{python}' -I -B '{module}' \"$@\"", payload)
            self.assertIn("PYTHONNOUSERSITE=1", payload)
            self.assertIn("PYTHONDONTWRITEBYTECODE=1", payload)
            self.assertNotIn(str(ROOT), payload)

            isolated_module = (
                runtime / "libexec/run_answer_blind_archon_isolated_campaign.py"
            )
            isolated_wrapper = runtime / "bin/answer-blind-archon-isolated-campaign"
            self.assertEqual(isolated_module.read_bytes(), ISOLATED_SOURCE.read_bytes())
            self.assertEqual(stat.S_IMODE(isolated_module.stat().st_mode), 0o444)
            isolated_payload = isolated_wrapper.read_text(encoding="utf-8")
            self.assertIn(
                f"exec '{python}' -I -B '{isolated_module}' \"$@\"",
                isolated_payload,
            )

            # Both paths are ordinary files under runtime_root, so the
            # production recursive runtime inventory necessarily binds them.
            inventory_paths = {
                path.relative_to(runtime).as_posix()
                for path in runtime.rglob("*")
                if path.is_file() and not path.is_symlink()
            }
            self.assertIn("libexec/run_answer_blind_gpt_campaign.py", inventory_paths)
            self.assertIn("bin/answer-blind-gpt-campaign", inventory_paths)
            self.assertIn(
                "libexec/run_answer_blind_archon_isolated_campaign.py",
                inventory_paths,
            )
            self.assertIn(
                "bin/answer-blind-archon-isolated-campaign", inventory_paths,
            )
            self.assertFalse(
                any(
                    path.name in INSTALLER.PYTHON_CACHE_DIRS
                    or path.suffix in {".pyc", ".pyo"}
                    for path in runtime.rglob("*")
                )
            )


if __name__ == "__main__":
    unittest.main()
