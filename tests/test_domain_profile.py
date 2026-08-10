"""Tests for project-level formalization domain profiles."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from archon.commands.tooling.domain_profile import load_domain_profile


class DomainProfileTests(unittest.TestCase):
    def test_legacy_defaults_remain_physlib_aware(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            profile = load_domain_profile(Path(directory))

        self.assertEqual(profile.name, "physics")
        self.assertEqual(profile.lean_search_packages, ("Mathlib", "Physlib"))
        self.assertTrue(profile.enforce_classical_physics_modeling)
        self.assertIn("import Physlib.Units.Basic", profile.preflight_lines)

    def test_quantum_profile_uses_exact_project_library(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            state = project / ".archon"
            state.mkdir()
            (state / "config.json").write_text(
                json.dumps(
                    {
                        "loop": {
                            "domain_profile": {
                                "name": "quantum-algorithms",
                                "display_name": "quantum algorithms",
                                "preflight_imports": [
                                    "Mathlib",
                                    "Cslib",
                                    "QAlgBench.Base",
                                ],
                                "lean_search_packages": [
                                    "Mathlib",
                                    "Cslib",
                                    "QAlgBench",
                                ],
                                "target_import_prefixes": ["QAlgBench"],
                                "enforce_classical_physics_modeling": False,
                                "require_explicit_mathlib_import": False,
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )

            profile = load_domain_profile(project)

        self.assertEqual(profile.name, "quantum-algorithms")
        self.assertEqual(
            profile.preflight_lines,
            ("import Mathlib", "import Cslib", "import QAlgBench.Base"),
        )
        self.assertEqual(profile.target_import_prefixes, ("QAlgBench",))
        self.assertFalse(profile.enforce_classical_physics_modeling)
        self.assertFalse(profile.require_explicit_mathlib_import)

    def test_chemistry_profile_exposes_specialized_marker_and_loop_modes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            state = project / ".archon"
            state.mkdir()
            (state / "config.json").write_text(
                json.dumps({
                    "loop": {
                        "domain_profile": {
                            "name": "chemistry",
                            "enforce_classical_physics_modeling": False,
                        }
                    }
                }),
                encoding="utf-8",
            )
            profile = load_domain_profile(project)

        self.assertEqual(
            profile.blueprint_markers,
            ("% archon:chemistry", "% archon:physics"),
        )
        self.assertEqual(
            profile.mode_for_stage("autoformalize"),
            "chemistry-formalize",
        )
        self.assertEqual(profile.mode_for_stage("prover"), "chemistry")
        self.assertIsNone(profile.mode_for_stage("review"))


if __name__ == "__main__":
    unittest.main()
