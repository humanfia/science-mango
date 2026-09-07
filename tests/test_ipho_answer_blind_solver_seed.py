from __future__ import annotations

import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "build_ipho_answer_blind_solver_seed.py"
)
SPEC = importlib.util.spec_from_file_location("ipho_solver_seed", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IphoAnswerBlindSolverSeedTests(unittest.TestCase):
    @staticmethod
    def _digest(data: bytes) -> str:
        return hashlib.sha256(data).hexdigest()

    def _lake_skeleton(self, root: Path) -> Path:
        lake = root / "lake"
        lake.mkdir()
        (lake / "lean-toolchain").write_text(
            MODULE.LEAN_VERSION + "\n", encoding="utf-8"
        )
        (lake / "lakefile.toml").write_text(
            f"""name = "ipho_2026_run"
version = "0.1.0"
defaultTargets = ["IPhO2026Run"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.31.0"

[[require]]
name = "PhysLean"
git = "https://github.com/HEPLean/PhysLean"
rev = "{MODULE.PHYSLIB_REV}"

[[lean_lib]]
name = "IPhO2026Run"
""",
            encoding="utf-8",
        )
        lake_manifest = {
            "version": "1.2.0",
            "packagesDir": ".lake/packages",
            "packages": [
                {
                    "name": "PhysLean",
                    "type": "git",
                    "url": "https://github.com/HEPLean/PhysLean",
                    "rev": MODULE.PHYSLIB_REV,
                    "subDir": None,
                },
                {
                    "name": "mathlib",
                    "type": "git",
                    "url": "https://github.com/leanprover-community/mathlib4",
                    "rev": MODULE.MATHLIB_REV,
                    "subDir": None,
                },
            ],
            "name": "ipho_2026_run",
            "lakeDir": ".lake",
            "fixedToolchain": False,
        }
        (lake / "lake-manifest.json").write_text(
            json.dumps(lake_manifest), encoding="utf-8"
        )
        return lake

    def _assets(self, root: Path) -> Path:
        assets = root / "safe-assets"
        (assets / "raw").mkdir(parents=True)
        (assets / "image").mkdir()
        for relative in MODULE.EXPECTED_PROBLEM_PDFS:
            paper = Path(relative).stem
            (assets / relative).write_bytes(
                b"%PDF-1.4\nproblem-only fixture "
                + paper.encode("ascii")
                + b"\n%%EOF\n"
            )
        for name in MODULE.EXPECTED_IMAGES:
            (assets / "image" / name).write_bytes(
                b"\x89PNG\r\n\x1a\nproblem-only fixture " + name.encode("ascii")
            )
        (assets / MODULE.THEORY_GENERAL_PDF).write_bytes(
            b"%PDF-1.4\ntheory general instructions\n%%EOF\n"
        )
        # These controller-only neighbors model the real source directory.  A
        # safe builder selects exact paths instead of recursively copying it.
        (assets / "raw" / "T1_solution.pdf").write_bytes(b"sealed solution")
        (assets / "raw" / "T1_marking_scheme.pdf").write_bytes(b"sealed marking")
        (assets / "reports").mkdir()
        (assets / "reports" / "old.md").write_text("sealed report", encoding="utf-8")
        return assets

    def _rows(self, assets: Path) -> list[dict]:
        images_by_paper = {
            paper: [
                name for name in MODULE.EXPECTED_IMAGES if name.startswith(f"{paper}_")
            ]
            for paper in ("T1", "T2", "T3", "E1")
        }
        paper_positions = {paper: 0 for paper in images_by_paper}
        rows: list[dict] = []
        for position, (identifier, index, paper) in enumerate(
            MODULE.EXPECTED_TARGETS, 1
        ):
            choices = images_by_paper[paper]
            image = choices[paper_positions[paper] % len(choices)]
            paper_positions[paper] += 1
            pdf_relative = f"raw/{paper}_problem.pdf"
            image_relative = f"image/{image}"
            pdf_data = (assets / pdf_relative).read_bytes()
            image_data = (assets / image_relative).read_bytes()
            general_data = (assets / MODULE.THEORY_GENERAL_PDF).read_bytes()
            problem_assets = [
                {
                    "kind": "problem_pdf",
                    "path": pdf_relative,
                    "sha256": self._digest(pdf_data),
                },
                {
                    "kind": "problem_page",
                    "path": image_relative,
                    "sha256": self._digest(image_data),
                },
            ]
            if paper != "E1":
                problem_assets.insert(
                    1,
                    {
                        "kind": "problem_general_instructions",
                        "path": MODULE.THEORY_GENERAL_PDF,
                        "sha256": self._digest(general_data),
                    },
                )
            rows.append(
                {
                    "schema_version": MODULE.SCHEMA_VERSION,
                    "protocol": MODULE.BLIND_PROTOCOL,
                    "evaluation_mode": "answer_blind",
                    "official_answer_seen": False,
                    "phase": "solve",
                    "id": identifier,
                    "index": index,
                    "source_index": f"source-{position}",
                    "problem_id": f"ipho_2026_{paper.lower()}",
                    "part_id": f"{paper}-part-{position}",
                    "question": f"## Physical scenario\n\nProblem-only context {position}.",
                    "current_question": f"Determine the physical quantity {position}.",
                    "shared_context": f"Problem-only context {position}.",
                    "category": "IPhO 2026",
                    "dataset": "IPhO 2026 official English problem materials",
                    "dataset_format": "native",
                    "paper": paper,
                    "kind": "experiment-derived" if paper == "E1" else "theory",
                    "formalization_ready": True,
                    "image": image,
                    "images": [image],
                    "previous_parts": [],
                    "source_page": position,
                    "printed_page": position,
                    "problem_assets": problem_assets,
                }
            )
        rows[1]["previous_parts"] = [
            {
                "source_id": rows[0]["id"],
                "part_id": rows[0]["part_id"],
                "question": rows[0]["current_question"],
                "dependency_policy": MODULE.DERIVE_POLICY,
            }
        ]
        return rows

    def _write_bundle(self, root: Path, rows: list[dict]) -> tuple[Path, Path]:
        controller = root / "controller"
        controller.mkdir(exist_ok=True)
        questions = controller / "questions_only.jsonl"
        bundle_data = b"".join(MODULE._json_bytes(row) for row in rows)
        questions.write_bytes(bundle_data)
        manifest = {
            "schema_version": MODULE.SCHEMA_VERSION,
            "protocol": MODULE.BLIND_PROTOCOL,
            "phase": "solve",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "row_count": len(rows),
            "blind_output": questions.name,
            "blind_sha256": self._digest(bundle_data),
            "targets": [
                {
                    "id": row["id"],
                    "index": row["index"],
                    "paper": row["paper"],
                    "blind_record_sha256": self._digest(MODULE._json_bytes(row)),
                }
                for row in rows
            ],
        }
        blind_manifest = controller / "questions_only.jsonl.manifest.json"
        blind_manifest.write_bytes(MODULE._json_bytes(manifest))
        return questions, blind_manifest

    def _fixture(self, root: Path) -> dict[str, object]:
        lake = self._lake_skeleton(root)
        assets = self._assets(root)
        rows = self._rows(assets)
        questions, blind_manifest = self._write_bundle(root, rows)
        return {
            "lake": lake,
            "assets": assets,
            "rows": rows,
            "questions": questions,
            "blind_manifest": blind_manifest,
            "output": root / "solver-seed",
        }

    def _build(self, paths: dict[str, object]) -> dict:
        return MODULE.build_seed(
            questions_only=paths["questions"],
            blind_manifest=paths["blind_manifest"],
            asset_root=paths["assets"],
            lake_root=paths["lake"],
            output_dir=paths["output"],
        )

    def test_builds_exact_minimal_seed_and_recursive_inventory(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            manifest = self._build(paths)
            seed = paths["output"]

            self.assertEqual(manifest["protocol"], MODULE.PROTOCOL)
            self.assertEqual(
                manifest["target_ids"], [row[0] for row in MODULE.EXPECTED_TARGETS]
            )
            self.assertEqual(
                manifest["isolation_claims"], {"filesystem": True, "network": False}
            )
            self.assertEqual(
                manifest["workspace_policy"],
                {
                    "fresh_git_init": True,
                    "history": False,
                    "remotes": [],
                    "solver_labels": ["GPT", "K3"],
                },
            )
            self.assertFalse((seed / ".git").exists())
            normalized_lakefile = (seed / "lakefile.toml").read_text(encoding="utf-8")
            self.assertIn('name = "Physlib"', normalized_lakefile)
            self.assertIn(MODULE.PHYSLIB_URL, normalized_lakefile)
            self.assertNotIn("PhysLean", normalized_lakefile)
            self.assertIn('name = "IPhO2026Problems"', normalized_lakefile)
            normalized_manifest = json.loads(
                (seed / "lake-manifest.json").read_text(encoding="utf-8")
            )
            physics_packages = [
                package
                for package in normalized_manifest["packages"]
                if package["name"] == "Physlib"
            ]
            self.assertEqual(len(physics_packages), 1)
            self.assertEqual(physics_packages[0]["url"], MODULE.PHYSLIB_URL)
            self.assertEqual(physics_packages[0]["rev"], MODULE.PHYSLIB_REV)
            self.assertEqual(
                {path.relative_to(seed).as_posix() for path in seed.rglob("*.lean")},
                {"IPhO2026Problems.lean", "IPhO2026Run.lean"},
            )
            self.assertNotIn(
                "problem_ipho_2026", (seed / "IPhO2026Problems.lean").read_text()
            )
            self.assertEqual(len(manifest["assets"]), 21)
            self.assertEqual(len(manifest["payload_files"]), 27)
            self.assertTrue(
                (seed / f"ipho_2026_source/{MODULE.THEORY_GENERAL_PDF}").is_file()
            )
            for forbidden in (
                "T1_solution.pdf",
                "T1_marking_scheme.pdf",
                "reports",
                "references",
                "blueprints",
            ):
                self.assertFalse(
                    any(path.name == forbidden for path in seed.rglob("*"))
                )
            self.assertEqual(MODULE.validate_seed(seed), manifest)

    def test_bound_general_instructions_is_required(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            (paths["assets"] / MODULE.THEORY_GENERAL_PDF).unlink()
            with self.assertRaisesRegex(MODULE.IsolationError, "does not exist"):
                self._build(paths)
            self.assertFalse(paths["output"].exists())

        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            theory = paths["rows"][0]
            theory["problem_assets"] = [
                asset
                for asset in theory["problem_assets"]
                if asset["kind"] != "problem_general_instructions"
            ]
            questions, blind_manifest = self._write_bundle(root, paths["rows"])
            paths["questions"] = questions
            paths["blind_manifest"] = blind_manifest
            with self.assertRaisesRegex(MODULE.IsolationError, "asset declarations"):
                self._build(paths)
            self.assertFalse(paths["output"].exists())

    def test_recursive_controller_field_leak_fails_before_output(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            paths["rows"][1]["previous_parts"][0]["official_answer"] = "sealed value"
            questions, blind_manifest = self._write_bundle(root, paths["rows"])
            paths["questions"] = questions
            paths["blind_manifest"] = blind_manifest
            with self.assertRaisesRegex(
                MODULE.IsolationError, "forbidden controller field"
            ):
                self._build(paths)
            self.assertFalse(paths["output"].exists())

    def test_declared_path_escape_and_asset_symlink_fail_closed(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            row = paths["rows"][0]
            row["image"] = "../T1_page-1.png"
            row["images"] = ["../T1_page-1.png"]
            row["problem_assets"][1]["path"] = "image/../T1_page-1.png"
            questions, blind_manifest = self._write_bundle(root, paths["rows"])
            paths["questions"] = questions
            paths["blind_manifest"] = blind_manifest
            with self.assertRaisesRegex(
                MODULE.IsolationError, "normalized project-relative"
            ):
                self._build(paths)
            self.assertFalse(paths["output"].exists())

        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            paths = self._fixture(root)
            image = paths["assets"] / "image" / MODULE.EXPECTED_IMAGES[0]
            data = image.read_bytes()
            image.unlink()
            outside = root / "outside.png"
            outside.write_bytes(data)
            image.symlink_to(outside)
            with self.assertRaisesRegex(MODULE.IsolationError, "symbolic link"):
                self._build(paths)
            self.assertFalse(paths["output"].exists())

    def test_manifest_or_lake_tamper_fails_before_atomic_publish(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            manifest = json.loads(paths["blind_manifest"].read_text(encoding="utf-8"))
            manifest["blind_sha256"] = "0" * 64
            paths["blind_manifest"].write_bytes(MODULE._json_bytes(manifest))
            with self.assertRaisesRegex(MODULE.IsolationError, "does not bind"):
                self._build(paths)
            self.assertFalse(paths["output"].exists())

        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            (paths["lake"] / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(MODULE.IsolationError, "requires exactly"):
                self._build(paths)
            self.assertFalse(paths["output"].exists())

    def test_recursive_validation_rejects_old_target_or_uninventoried_file(self):
        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            self._build(paths)
            seed = paths["output"]
            targets = seed / "IPhO2026Problems"
            targets.mkdir()
            (targets / "problem_ipho_2026_t1_a1.lean").write_text(
                "theorem leaked : True := by trivial\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(MODULE.IsolationError, "old IPhO Lean target"):
                MODULE.validate_seed(seed)

        with tempfile.TemporaryDirectory() as raw:
            paths = self._fixture(Path(raw))
            self._build(paths)
            seed = paths["output"]
            (seed / "untracked.txt").write_text("extra", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.IsolationError, "inventory mismatch"):
                MODULE.validate_seed(seed)


if __name__ == "__main__":
    unittest.main()
