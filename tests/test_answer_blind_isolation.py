from __future__ import annotations

import importlib.util
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "build_answer_blind_solver_seed.py"
)
SPEC = importlib.util.spec_from_file_location("answer_blind_seed_builder", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class AnswerBlindIsolationTests(unittest.TestCase):
    COMMIT = "a" * 40

    def _fixture(self, root: Path) -> dict[str, Path | list[str]]:
        source = root / "patched-source"
        engine = source / "src" / "archon"
        package_data = engine / ".archon-src" / "prompts"
        package_data.mkdir(parents=True)
        (source / "pyproject.toml").write_text(
            '[project]\nname = "archon"\nversion = "0.0.0"\n',
            encoding="utf-8",
        )
        (source / "MANIFEST.in").write_text(
            "recursive-include src/archon/.archon-src *\n", encoding="utf-8"
        )
        (engine / "__init__.py").write_text("VERSION = 1\n", encoding="utf-8")
        (package_data / "prove.md").write_text(
            "Derive the requested theorem from the problem.\n", encoding="utf-8"
        )
        # Generated files are explicitly ignored, rather than copied.
        cache = engine / "__pycache__"
        cache.mkdir()
        (cache / "engine.pyc").write_bytes(b"cache")

        lake = source / "icho_2026_run"
        for relative, contents in {
            "lakefile.toml": 'name = "icho_seed"\n',
            "lake-manifest.json": '{"version":"1.2.0","packages":[]}\n',
            "lean-toolchain": "leanprover/lean4:v4.31.0\n",
            "IChO2026Run/Basic.lean": "import Mathlib\n",
            "IChO2026Run/Dependencies.lean": "import Mathlib\n",
            "IChO2026Chem.lean": (
                "import IChO2026Chem.Core\n"
                "import IChO2026Chem.Reporting\n"
            ),
            "IChO2026Chem/Core.lean": "import Mathlib\nnamespace IChO2026Chem\nend IChO2026Chem\n",
            "IChO2026Chem/Reporting.lean": (
                "import Mathlib\n"
                "namespace IChO2026Chem.Reporting\n"
                "def finalOnly : Prop := True\n"
                "end IChO2026Chem.Reporting\n"
            ),
            ".gitignore": ".lake/\n.archon/\n",
            "archon-protected.yaml": "files: []\n",
        }.items():
            path = lake / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents, encoding="utf-8")

        images = root / "controller-images"
        images.mkdir()
        (images / "T1_page-1.png").write_bytes(b"problem image")
        pdf = root / "theory_problem.pdf"
        pdf.write_bytes(b"problem pdf")
        image_sha = hashlib.sha256(b"problem image").hexdigest()
        pdf_sha = hashlib.sha256(b"problem pdf").hexdigest()
        bundle = root / "questions_only.jsonl"
        bundle.write_text(
            json.dumps(
                {
                    "id": "icho_2026_t1_a1",
                    "evaluation_mode": "answer_blind",
                    "official_answer_seen": False,
                    "phase": "solve",
                    "current_question": "Calculate the requested amount.",
                    "images": ["T1_page-1.png"],
                    "source_pdf": "theory_problem.pdf",
                    "problem_assets": [
                        {
                            "kind": "problem_page",
                            "path": "T1_page-1.png",
                            "sha256": image_sha,
                        },
                        {
                            "kind": "problem_pdf",
                            "path": "theory_problem.pdf",
                            "sha256": pdf_sha,
                        },
                    ],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        return {
            "source": source,
            "lake": lake,
            "images": images,
            "pdf": pdf,
            "bundle": bundle,
            "problem_images": ["T1_page-1.png"],
        }

    def _build(self, paths: dict[str, Path | list[str]], output: Path, **kwargs):
        options = {
            "source_root": paths["source"],
            "lake_root": paths["lake"],
            "questions_only": paths["bundle"],
            "problem_pdf": paths["pdf"],
            "image_root": paths["images"],
            "problem_images": paths["problem_images"],
            "output_dir": output,
            "source_commit": self.COMMIT,
        }
        options.update(kwargs)
        return MODULE.build_seed(**options)

    def test_explicit_projection_omits_git_old_problems_and_run_evidence(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            source = paths["source"]
            lake = paths["lake"]
            assert isinstance(source, Path) and isinstance(lake, Path)
            (source / ".git").mkdir()
            (source / ".git" / "config").write_text(
                '[remote "origin"]\nurl = https://example.test/private.git\n',
                encoding="utf-8",
            )
            (lake / "IChO2026Problems.lean").write_text(
                "theorem old_result : True := by trivial\n", encoding="utf-8"
            )
            kinetics = lake / "IChO2026Chem" / "Kinetics"
            kinetics.mkdir()
            (kinetics / "PriorOfficialResult.lean").write_text(
                "theorem old_result : True := by trivial\n", encoding="utf-8"
            )
            for directory in ("blueprint", "reports", "references"):
                evidence = lake / directory
                evidence.mkdir()
                (evidence / "prior.txt").write_text("prior run", encoding="utf-8")

            seed = root / "seed"
            manifest = self._build(paths, seed)

            self.assertFalse((seed / ".git").exists())
            self.assertEqual(
                (seed / "IChO2026Problems.lean").read_text(encoding="utf-8").splitlines()[0],
                "import IChO2026Chem",
            )
            self.assertIn(
                "import IChO2026Problems.All",
                (seed / "IChO2026Problems.lean").read_text(encoding="utf-8"),
            )
            self.assertIn(
                "import IChO2026Problems",
                (seed / "IChO2026Run.lean").read_text(encoding="utf-8"),
            )
            self.assertTrue((seed / "IChO2026Chem/Reporting.lean").is_file())
            self.assertFalse((seed / "IChO2026Chem/Kinetics").exists())
            self.assertFalse((seed / "blueprint").exists())
            self.assertFalse((seed / "reports").exists())
            self.assertFalse((seed / "references").exists())
            self.assertFalse((seed / "src").exists())
            self.assertFalse((seed / "pyproject.toml").exists())
            self.assertEqual(manifest["engine_files"], {})
            self.assertIs(manifest["source_revision_disclosed"], False)
            self.assertNotIn("source_commit", manifest)
            self.assertEqual(
                manifest["isolation_claims"], {"filesystem": True, "network": False}
            )
            self.assertEqual(MODULE.validate_seed(seed), manifest)

    def test_chemistry_umbrella_cannot_reintroduce_kinetics(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            lake = paths["lake"]
            assert isinstance(lake, Path)
            (lake / "IChO2026Chem.lean").write_text(
                "import IChO2026Chem.Core\n"
                "import IChO2026Chem.Reporting\n"
                "import IChO2026Chem.Kinetics.PriorOfficialResult\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(MODULE.IsolationError, "Kinetics"):
                self._build(paths, root / "seed")

    def test_bundle_asset_contract_rejects_missing_extra_and_substituted_assets(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            with self.subTest("extra"):
                images = paths["images"]
                assert isinstance(images, Path)
                (images / "extra.png").write_bytes(b"unlisted source material")
                with self.assertRaisesRegex(MODULE.IsolationError, "does not match"):
                    self._build(
                        paths,
                        root / "extra-seed",
                        problem_images=["T1_page-1.png", "extra.png"],
                    )
            with self.subTest("missing"):
                with self.assertRaisesRegex(MODULE.IsolationError, "does not match"):
                    self._build(paths, root / "missing-seed", problem_images=[])
            with self.subTest("substituted"):
                images = paths["images"]
                assert isinstance(images, Path)
                (images / "T1_page-1.png").write_bytes(b"different bytes")
                with self.assertRaisesRegex(MODULE.IsolationError, "hash does not match"):
                    self._build(paths, root / "changed-seed")

    def test_controller_engine_tree_is_never_copied_into_solver_seed(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            source = paths["source"]
            assert isinstance(source, Path)
            (source / "src" / "archon" / "theory_solution.txt").write_text(
                "official result", encoding="utf-8"
            )
            output = root / "seed"
            self._build(paths, output)
            self.assertFalse((output / "src").exists())
            self.assertFalse((output / "theory_solution.txt").exists())

    def test_nested_engine_git_metadata_is_not_projected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            source = paths["source"]
            assert isinstance(source, Path)
            nested_git = source / "src" / "archon" / ".git"
            nested_git.mkdir()
            (nested_git / "config").write_text("[core]\n", encoding="utf-8")
            output = root / "seed"
            self._build(paths, output)
            self.assertFalse((output / "src").exists())

    def test_answer_field_at_any_json_depth_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            bundle = paths["bundle"]
            assert isinstance(bundle, Path)
            bundle.write_text(
                json.dumps(
                    {
                        "id": "bad",
                        "official_answer_seen": False,
                        "nested": [{"answer": "controller secret"}],
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(MODULE.IsolationError, "answer-bearing field"):
                self._build(paths, root / "seed")

    def test_credential_field_and_absolute_problem_path_are_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            bundle = paths["bundle"]
            assert isinstance(bundle, Path)
            for malicious, expected in (
                ({"nested": {"api_key": "not-for-the-solver"}}, "credential field"),
                ({"source_path": "/tmp/controller/sealed.jsonl"}, "absolute"),
            ):
                with self.subTest(expected=expected):
                    row = {
                        "id": "bad",
                        "official_answer_seen": False,
                        **malicious,
                    }
                    bundle.write_text(json.dumps(row) + "\n", encoding="utf-8")
                    with self.assertRaisesRegex(MODULE.IsolationError, expected):
                        self._build(paths, root / f"seed-{expected.replace(' ', '-')}")

    def test_unselected_engine_symlink_is_not_projected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            source = paths["source"]
            assert isinstance(source, Path)
            outside = root / "outside.py"
            outside.write_text("LEAK = True\n", encoding="utf-8")
            link = source / "src" / "archon" / "leak.py"
            try:
                link.symlink_to(outside)
            except OSError as exc:  # pragma: no cover - symlinks may be disabled
                self.skipTest(f"symbolic links unavailable: {exc}")
            output = root / "seed"
            self._build(paths, output)
            self.assertFalse((output / "src").exists())

    def test_deterministic_manifest_and_dry_validation(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            dry_output = root / "dry-output"
            dry_manifest = self._build(
                paths, dry_output, dry_run=True, output_dir=dry_output
            )
            self.assertFalse(dry_output.exists())

            first = root / "seed-one"
            second = root / "seed-two"
            first_manifest = self._build(paths, first)
            second_manifest = self._build(paths, second)
            self.assertEqual(dry_manifest, first_manifest)
            self.assertEqual(first_manifest, second_manifest)
            self.assertEqual(
                (first / MODULE.MANIFEST_NAME).read_bytes(),
                (second / MODULE.MANIFEST_NAME).read_bytes(),
            )
            self.assertEqual(
                first_manifest["blind_bundle_sha256"],
                first_manifest["blind_bundle"]["sha256"],
            )
            self.assertEqual(
                set(first_manifest["assets"]),
                {
                    "icho_2026_source/image/T1_page-1.png",
                    "icho_2026_source/raw/theory_problem.pdf",
                },
            )

    def test_gpt_and_k3_copies_are_fresh_unrelated_repositories(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            seed = root / "seed"
            self._build(paths, seed)
            gpt = root / "gpt-workspace"
            k3 = root / "k3-workspace"
            MODULE.copy_seed_for_gpt_and_k3(
                seed, gpt_workspace=gpt, k3_workspace=k3
            )

            for workspace in (gpt, k3):
                self.assertTrue((workspace / ".git").is_dir())
                self.assertEqual(
                    subprocess.run(
                        ["git", "-C", str(workspace), "remote"],
                        check=True,
                        capture_output=True,
                        text=True,
                    ).stdout,
                    "",
                )
                self.assertEqual(
                    subprocess.run(
                        ["git", "-C", str(workspace), "rev-list", "--all"],
                        check=True,
                        capture_output=True,
                        text=True,
                    ).stdout,
                    "",
                )
                self.assertEqual(
                    (workspace / MODULE.MANIFEST_NAME).read_bytes(),
                    (seed / MODULE.MANIFEST_NAME).read_bytes(),
                )
            self.assertNotEqual((gpt / ".git").resolve(), (k3 / ".git").resolve())


if __name__ == "__main__":
    unittest.main()
