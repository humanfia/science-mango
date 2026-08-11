"""Regression tests for the neutral IChO 2026 dataset exporter."""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


_EXPORTER_PATH = (
    Path(__file__).resolve().parents[1]
    / "icho_2026_run"
    / "scripts"
    / "export_hf_dataset.py"
)
_SPEC = importlib.util.spec_from_file_location("icho_hf_export", _EXPORTER_PATH)
assert _SPEC is not None and _SPEC.loader is not None
_EXPORTER = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = _EXPORTER
_SPEC.loader.exec_module(_EXPORTER)


class LeanSourcePolicyTest(unittest.TestCase):
    def test_comments_and_strings_do_not_create_false_placeholder_hits(self):
        source = (
            "/- outer sorry /- axiom hidden : Prop -/ admit -/\n"
            '-- "native_decide" and sorryAx are prose\n'
            'def message := "sorry admit axiom native_decide"\n'
            "theorem complete : True := by trivial\n"
        )
        _EXPORTER._validate_lean_source(Path("Complete.lean"), source)

    def test_each_active_prohibited_construct_is_rejected(self):
        snippets = {
            "sorry": "theorem bad : True := by sorry\n",
            "admit": "theorem bad : True := by admit\n",
            "axiom": "axiom bad : True\n",
            "native_decide": "theorem bad : True := by native_decide\n",
            "sorryAx": "theorem bad : True := sorryAx _ true\n",
        }
        for token, source in snippets.items():
            with self.subTest(token=token):
                with self.assertRaisesRegex(_EXPORTER.ExportError, token):
                    _EXPORTER._validate_lean_source(Path("Bad.lean"), source)


class PublicBundlePolicyTest(unittest.TestCase):
    def test_sensitive_or_non_neutral_text_is_rejected(self):
        cases = {
            "workflow": "Ar" + "chon internal label",
            "marker": "USER requested shortcut",
            "hf_secret": "hf_" + "A" * 24,
            "api_secret": "sk-" + "B" * 24,
            "absolute_path": "/root/private/result.json",
        }
        for name, content in cases.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as td:
                bundle = Path(td)
                (bundle / "record.txt").write_text(content, encoding="utf-8")
                with self.assertRaises(_EXPORTER.ExportError):
                    _EXPORTER._validate_public_bundle(bundle)

    def test_each_stale_workflow_phrase_is_rejected_case_insensitively(self):
        cases = {
            "redraft": "This needs a ReDrAfT before release.",
            "autoformalize": "Run AUTOFORMALIZE on the prompt.",
            "autoformalization": "The AutoFormalization stage is pending.",
            "proof_bodies_left": "Proof Bodies Are Left As placeholders.",
            "compiling_sorry_file": (
                "CREATE A COMPILING LEAN FILE WITH SORRY BODIES first."
            ),
            "not_proof_task": "This is NOT A PROOF TASK for the worker.",
            "by_sorry": "Temporary implementation: By SoRrY."
        }
        for name, content in cases.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as td:
                bundle = Path(td)
                (bundle / "record.txt").write_text(content, encoding="utf-8")
                with self.assertRaisesRegex(
                    _EXPORTER.ExportError, "stale workflow prose"
                ):
                    _EXPORTER._validate_public_bundle(bundle)

    def test_nearby_release_language_is_not_mistaken_for_stale_prose(self):
        with tempfile.TemporaryDirectory() as td:
            bundle = Path(td)
            (bundle / "record.txt").write_text(
                "A complete formalization with checked proof bodies.\n",
                encoding="utf-8",
            )
            _EXPORTER._validate_public_bundle(bundle)

    def test_project_relative_source_path_is_not_mistaken_for_absolute(self):
        with tempfile.TemporaryDirectory() as td:
            bundle = Path(td)
            (bundle / "record.txt").write_text(
                "Visual evidence: ../icho_2026_source/image/T9_page-1.png\n",
                encoding="utf-8",
            )
            _EXPORTER._validate_public_bundle(bundle)

    def test_banned_directories_are_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            bundle = Path(td)
            hidden = bundle / ".lake"
            hidden.mkdir()
            (hidden / "state.txt").write_text("cache", encoding="utf-8")
            with self.assertRaisesRegex(_EXPORTER.ExportError, "prohibited path"):
                _EXPORTER._validate_public_bundle(bundle)


class ExportIntegrationTest(unittest.TestCase):
    def _load_project_exporter(self, project: Path):
        exporter_path = project / "scripts" / "export_hf_dataset.py"
        module_index = 0
        while True:
            module_name = f"icho_hf_export_fixture_{module_index}"
            if module_name not in sys.modules:
                break
            module_index += 1
        spec = importlib.util.spec_from_file_location(module_name, exporter_path)
        assert spec is not None and spec.loader is not None
        exporter = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = exporter
        try:
            spec.loader.exec_module(exporter)
        except BaseException:
            sys.modules.pop(module_name, None)
            raise
        self.addCleanup(sys.modules.pop, module_name, None)
        return exporter

    def _make_project(self, root: Path, target_count: int = 32) -> Path:
        repo = root / "repo"
        project = repo / "icho_2026_run"
        problems = project / "IChO2026Problems"
        reports = project / "reports" / "icho_2026"
        references = project / "references"
        chemistry = project / "IChO2026Chem"
        run_sources = project / "IChO2026Run"
        scripts = project / "scripts"
        for directory in (
            problems,
            reports,
            references,
            chemistry,
            run_sources,
            scripts,
        ):
            directory.mkdir(parents=True, exist_ok=True)

        inventory: list[dict[str, object]] = []
        imports: list[str] = []
        for number in range(1, target_count + 1):
            record_id = f"icho_2026_t1_a{number}"
            filename = f"problem_{record_id}.lean"
            relative = f"IChO2026Problems/{filename}"
            entry: dict[str, object] = {
                "id": record_id,
                "source_index": f"T1-A{number}",
                "problem_id": "icho_2026_t1",
                "part_id": f"T1-A{number}",
                "current_question": f"Question {number}",
                "shared_context": "Shared chemistry context",
                "answer": f"Official answer {number}",
                "category": "IChO 2026 Theory",
                "dataset": "Official English exam materials",
                "points": 1.0,
                "paper": "T1",
                # `kind` is an answer modality.  Theory papers may contain
                # classification tasks, as the real T5-A1 and T6-A3 do.
                "kind": "classification" if number == 1 else "theory",
                "previous_parts": [],
                "source_url": "https://example.test/problem.pdf",
                "solution_url": "https://example.test/solution.pdf",
                "images": ["T1_page-1.png"],
                "source_pdf": "theory_problem.pdf",
                "source_page": 1,
                "printed_page": 1,
                "solution_pdf": "theory_solution.pdf",
            }
            inventory.append(entry)
            report = {"entry": entry, "output_lean": relative}
            (reports / f"{filename.removesuffix('.lean')}.source.json").write_text(
                json.dumps(report), encoding="utf-8"
            )
            module = relative.removesuffix(".lean").replace("/", ".")
            imports.append(f"import {module}")
            (problems / filename).write_text(
                f"theorem result_{number} : True := by trivial\n", encoding="utf-8"
            )

        (references / "icho_2026_theory_ready.jsonl").write_text(
            "".join(json.dumps(entry) + "\n" for entry in inventory),
            encoding="utf-8",
        )
        (project / "IChO2026Problems.lean").write_text(
            "\n".join(imports) + "\n", encoding="utf-8"
        )
        (project / "IChO2026Chem.lean").write_text(
            "import IChO2026Chem.Core\n", encoding="utf-8"
        )
        (chemistry / "Core.lean").write_text(
            "def chemistryReady : True := True\n", encoding="utf-8"
        )
        (project / "IChO2026Run.lean").write_text(
            "import IChO2026Problems\n", encoding="utf-8"
        )
        (run_sources / "Basic.lean").write_text(
            "def runReady : True := True\n", encoding="utf-8"
        )
        (project / "lean-toolchain").write_text(
            "leanprover/lean4:v4.31.0\n", encoding="utf-8"
        )
        (project / "lakefile.toml").write_text(
            'name = "icho_2026_run"\n', encoding="utf-8"
        )
        (project / "lake-manifest.json").write_text(
            '{"version":"1.2.0","packages":[]}\n', encoding="utf-8"
        )
        (scripts / "export_hf_dataset.py").write_text(
            _EXPORTER_PATH.read_text(encoding="utf-8"), encoding="utf-8"
        )
        helper_path = _EXPORTER_PATH.with_name("select_theory_targets.py")
        (scripts / "select_theory_targets.py").write_text(
            helper_path.read_text(encoding="utf-8"), encoding="utf-8"
        )
        (repo / "LICENSE").write_text("Apache License 2.0\n", encoding="utf-8")
        return project

    def _commit_project(self, project: Path) -> str:
        repo = project.parent
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
        subprocess.run(
            ["git", "config", "user.email", "test@example.test"], cwd=repo, check=True
        )
        subprocess.run(["git", "config", "user.name", "Test"], cwd=repo, check=True)
        subprocess.run(["git", "add", "."], cwd=repo, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=repo, check=True)
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=repo, text=True
        ).strip()

    def test_exports_exact_neutral_reproducible_bundle(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            project = self._make_project(root)
            commit = self._commit_project(project)
            output = root / "bundle"
            exporter = self._load_project_exporter(project)

            self.assertEqual(exporter.export(project, output), output.resolve())
            records = [
                json.loads(line)
                for line in (output / "data" / "icho_2026_lean.jsonl")
                .read_text(encoding="utf-8")
                .splitlines()
            ]
            self.assertEqual(len(records), 32)
            self.assertEqual(
                set(records[0]),
                {"schema_version", "id", "source", "formalization", "provenance"},
            )
            self.assertEqual(records[0]["schema_version"], "1.0")
            self.assertEqual(records[0]["provenance"]["source_commit"], commit)
            self.assertEqual(records[0]["source"]["paper"], "T1")
            self.assertEqual(records[0]["source"]["kind"], "classification")
            self.assertIn("official_answer", records[0]["source"])
            self.assertIn("source", records[0]["formalization"])
            self.assertTrue((output / "lean" / "lakefile.toml").is_file())
            self.assertTrue((output / "metadata" / "manifest.json").is_file())
            self.assertTrue((output / "checksums.sha256").is_file())
            self.assertIn(
                "Each JSONL row has five top-level fields:",
                (output / "README.md").read_text(encoding="utf-8"),
            )
            self.assertFalse((output / "blueprints").exists())
            self.assertFalse((output / "scripts").exists())
            self.assertFalse((output / "reports").exists())
            self.assertFalse((output / "references").exists())
            exporter._validate_public_bundle(output)

    def test_rejects_any_target_count_other_than_release_contract(self):
        with tempfile.TemporaryDirectory() as td:
            project = self._make_project(Path(td), target_count=31)
            with self.assertRaisesRegex(_EXPORTER.ExportError, "exactly 32"):
                _EXPORTER._load_targets(project)

    def test_rejects_practical_paper_even_when_kind_says_theory(self):
        with tempfile.TemporaryDirectory() as td:
            project = self._make_project(Path(td))
            inventory_path = project / "references" / "icho_2026_theory_ready.jsonl"
            first_line = inventory_path.read_text(encoding="utf-8").splitlines()[0]
            entry = json.loads(first_line)
            entry["paper"] = "P1"
            entry["kind"] = "theory"
            with self.assertRaisesRegex(_EXPORTER.ExportError, "non-theory paper"):
                _EXPORTER._validate_inventory_entry(entry, inventory_path)

    def test_rejects_dirty_or_untracked_release_sources(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            project = self._make_project(root)
            self._commit_project(project)
            target = sorted((project / "IChO2026Problems").glob("*.lean"))[0]
            target.write_text("theorem changed : True := by trivial\n", encoding="utf-8")
            output = root / "bundle"
            exporter = self._load_project_exporter(project)
            with self.assertRaisesRegex(exporter.ExportError, "tracked and clean"):
                exporter.export(project, output)
            self.assertFalse(output.exists())

    def test_rejects_committed_data_with_dirty_exporter(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            project = self._make_project(root)
            self._commit_project(project)
            exporter = project / "scripts" / "export_hf_dataset.py"
            exporter.write_text(
                exporter.read_text(encoding="utf-8")
                + "\n# uncommitted exporter change\n",
                encoding="utf-8",
            )
            exporter_module = self._load_project_exporter(project)

            output = root / "bundle"
            with self.assertRaisesRegex(
                exporter_module.ExportError, "tracked and clean"
            ):
                exporter_module.export(project, output)
            self.assertFalse(output.exists())

    def test_rejects_ignored_untracked_exporter(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            project = self._make_project(root)
            exporter = project / "scripts" / "export_hf_dataset.py"
            exporter_source = exporter.read_text(encoding="utf-8")
            exporter.unlink()
            (project.parent / ".gitignore").write_text(
                "icho_2026_run/scripts/export_hf_dataset.py\n", encoding="utf-8"
            )
            self._commit_project(project)
            exporter.write_text(exporter_source, encoding="utf-8")
            exporter_module = self._load_project_exporter(project)

            output = root / "bundle"
            with self.assertRaisesRegex(
                exporter_module.ExportError, "untracked=.*export"
            ):
                exporter_module.export(project, output)
            self.assertFalse(output.exists())

    def test_rejects_dirty_or_ignored_untracked_schema_helper(self):
        helper_relative = Path("scripts/select_theory_targets.py")
        for state in ("dirty", "ignored-untracked"):
            with self.subTest(state=state), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                project = self._make_project(root)
                helper = project / helper_relative
                helper_source = helper.read_text(encoding="utf-8")
                if state == "ignored-untracked":
                    helper.unlink()
                    (project.parent / ".gitignore").write_text(
                        f"icho_2026_run/{helper_relative.as_posix()}\n",
                        encoding="utf-8",
                    )
                self._commit_project(project)
                helper.write_text("# uncommitted helper change\n", encoding="utf-8")
                if state == "ignored-untracked":
                    helper.write_text(helper_source, encoding="utf-8")
                exporter = self._load_project_exporter(project)

                output = root / "bundle"
                with self.assertRaisesRegex(
                    exporter.ExportError, "tracked and clean|untracked="
                ):
                    exporter.export(project, output)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
