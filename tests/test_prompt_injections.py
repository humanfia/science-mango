"""Tests for the auto-injected prompt blocks the loop replaces agent file-reads with.

The user's design principle: anything the loop can do deterministically
should be done in code and *injected* into the prompt — not asked of
the agent as "go read file X then clear it". Two blocks under test:

* ``_user_hints_block`` — renders the captured USER_HINTS.md text
  inline (the loop captures + clears the file; the agent never sees
  the file system path).
* ``_blueprint_doctor_findings_block`` — reads the prior iter's
  ``blueprint-doctor.json`` and renders the live findings inline so
  the agent doesn't have to open the report.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from archon.prompts import (
    _blueprint_doctor_findings_block,
    _user_hints_block,
    build_dag_prompt,
    build_plan_prompt,
    build_review_prompt,
)


class UserHintsBlockTest(unittest.TestCase):
    def test_empty_renders_fallback_affordance(self):
        block = _user_hints_block(None)
        self.assertIn("## User hints", block)
        self.assertIn("No user hints this iteration", block)
        # The fallback rule appears wrapped — collapse whitespace
        # when checking the phrase.
        normalized = " ".join(block.split())
        self.assertIn("Fallback if no user response", normalized)

    def test_empty_string_treated_as_no_hints(self):
        self.assertIn("No user hints", _user_hints_block(""))
        self.assertIn("No user hints", _user_hints_block("   \n  \n"))

    def test_non_empty_renders_captured_text(self):
        hints = "- [2026-05-18T12:00:00Z] focus on the M2.a route this iter"
        block = _user_hints_block(hints)
        self.assertIn("## User hints", block)
        self.assertIn("focus on the M2.a route this iter", block)
        # The block must declare that the loop will clear the file —
        # otherwise the agent re-reads + re-clears it (defeats the move).
        self.assertIn("clear", block.lower())
        self.assertIn("do NOT need to read", block)

    def test_html_comment_only_treated_as_no_hints(self):
        # The bundled USER_HINTS.md template is an HTML-comment
        # preamble. Template-only content must render as "no hints" —
        # otherwise the planner sees the format guide as live
        # instructions.
        block = _user_hints_block(
            "<!-- format guide for the user; not a hint -->\n"
        )
        self.assertIn("No user hints", block)

    def test_html_comment_stripped_when_bullets_present(self):
        # Real hints + preamble: only the bullets should reach the
        # planner; the comment preamble must be stripped.
        block = _user_hints_block(
            "<!-- format guide -->\n"
            "- [2026-05-18T12:00:00Z] focus on the M2.a route\n"
        )
        self.assertIn("focus on the M2.a route", block)
        self.assertNotIn("format guide", block)


class BlueprintDoctorFindingsBlockTest(unittest.TestCase):
    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        self.state = Path(self._td.name) / ".archon"
        self.state.mkdir()

    def tearDown(self):
        self._td.cleanup()

    def _write_prior_doctor(self, iter_num: int, payload: dict) -> Path:
        prev = iter_num - 1
        d = self.state / "logs" / f"iter-{prev:03d}"
        d.mkdir(parents=True, exist_ok=True)
        p = d / "blueprint-doctor.json"
        p.write_text(json.dumps(payload), encoding="utf-8")
        return p

    def test_empty_when_iter_one(self):
        # No prior iter — block stays empty.
        self.assertEqual(
            _blueprint_doctor_findings_block(self.state, 1), "",
        )

    def test_empty_when_prior_file_missing(self):
        self.assertEqual(
            _blueprint_doctor_findings_block(self.state, 5), "",
        )

    def test_empty_when_no_findings_in_prior(self):
        self._write_prior_doctor(5, {
            "orphan_chapters": [],
            "broken_refs": [],
            "axiom_decls": [],
        })
        self.assertEqual(
            _blueprint_doctor_findings_block(self.state, 5), "",
        )

    def test_renders_orphans(self):
        self._write_prior_doctor(5, {
            "orphan_chapters": [
                "/proj/blueprint/src/chapters/Foo.tex",
                "/proj/blueprint/src/chapters/Bar.tex",
            ],
            "broken_refs": [],
            "axiom_decls": [],
        })
        block = _blueprint_doctor_findings_block(self.state, 5)
        self.assertIn("## Blueprint doctor", block)
        self.assertIn("Orphan chapters", block)
        self.assertIn("Foo.tex", block)
        self.assertIn("Bar.tex", block)

    def test_renders_broken_refs_grouped_by_chapter(self):
        self._write_prior_doctor(5, {
            "orphan_chapters": [],
            "broken_refs": [
                {"chapter": "/proj/blueprint/src/chapters/A.tex",
                 "kind": "ref", "label": "thm:missing"},
                {"chapter": "/proj/blueprint/src/chapters/A.tex",
                 "kind": "uses", "label": "lem:also_missing"},
                {"chapter": "/proj/blueprint/src/chapters/B.tex",
                 "kind": "cref", "label": "def:gone"},
            ],
            "axiom_decls": [],
        })
        block = _blueprint_doctor_findings_block(self.state, 5)
        self.assertIn("Broken cross-references", block)
        self.assertIn("thm:missing", block)
        self.assertIn("lem:also_missing", block)
        self.assertIn("def:gone", block)
        # Grouped by chapter — A.tex appears once, with its two refs
        # underneath as sub-bullets.
        a_count = block.count("A.tex")
        self.assertEqual(a_count, 1, f"expected A.tex grouped once, got {a_count}")

    def test_renders_malformed_annotations(self):
        self._write_prior_doctor(5, {
            "orphan_chapters": [],
            "broken_refs": [],
            "malformed_refs": [
                {"chapter": "/proj/blueprint/src/chapters/A.tex",
                 "kind": "uses", "reason": "empty argument"},
                {"chapter": "/proj/blueprint/src/chapters/A.tex",
                 "kind": "uses", "reason": "empty list item"},
                {"chapter": "/proj/blueprint/src/chapters/B.tex",
                 "kind": "label", "reason": "empty argument"},
            ],
            "axiom_decls": [],
        })
        block = _blueprint_doctor_findings_block(self.state, 5)
        self.assertIn("Malformed annotations", block)
        self.assertIn("empty argument", block)
        self.assertIn("empty list item", block)
        # The block must explicitly warn that this is what crashes
        # the leanblueprint build.
        self.assertIn("crash", block.lower())

    def test_renders_axiom_decls(self):
        self._write_prior_doctor(5, {
            "orphan_chapters": [],
            "broken_refs": [],
            "axiom_decls": [
                {"file": "/proj/Foo.lean", "name": "magic_axiom"},
            ],
        })
        block = _blueprint_doctor_findings_block(self.state, 5)
        self.assertIn("Axiom declarations", block)
        self.assertIn("magic_axiom", block)
        self.assertIn("no new axioms", block.lower())

    def test_renders_physics_grounding_problems(self):
        self._write_prior_doctor(5, {
            "orphan_chapters": [],
            "broken_refs": [],
            "axiom_decls": [],
            "physics_grounding_problems": [
                {
                    "file": "/proj/Phys.lean",
                    "kind": "missing-grounding-log",
                    "reason": "Phys.lean has no LeanExplore grounding log",
                },
            ],
        })
        block = _blueprint_doctor_findings_block(self.state, 5)
        self.assertIn("Physics grounding problems", block)
        self.assertIn("Phys.lean", block)
        self.assertIn("LeanExplore grounding log", block)

    def test_caps_huge_orphan_list(self):
        payload = {
            "orphan_chapters": [f"/p/chapters/Orphan{i:03d}.tex" for i in range(50)],
            "broken_refs": [],
            "axiom_decls": [],
        }
        self._write_prior_doctor(5, payload)
        block = _blueprint_doctor_findings_block(
            self.state, 5, max_orphans=10,
        )
        # First 10 entries are rendered (0-indexed 000..009).
        self.assertIn("Orphan000.tex", block)
        self.assertIn("Orphan009.tex", block)
        # The 11th entry (010) is beyond the cap.
        self.assertNotIn("Orphan010.tex", block)
        self.assertIn("and 40 more", block)


class BuildPlanPromptIntegrationTest(unittest.TestCase):
    """Verify the captured hints and doctor findings flow through
    ``build_plan_prompt`` and land in the final prompt text."""

    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        self.state = self.root / ".archon"
        self.state.mkdir()
        (self.state / "subagents").mkdir()

    def tearDown(self):
        self._td.cleanup()

    def test_captured_hints_appear_in_prompt(self):
        hints_text = "- [ts] please focus on M2.a this iter"
        prompt = build_plan_prompt(
            project_name="proj",
            project_path=self.root,
            state_dir=self.state,
            stage="prover",
            iter_num=7,
            captured_user_hints=hints_text,
        )
        self.assertIn("## User hints", prompt)
        self.assertIn("please focus on M2.a this iter", prompt)
        # Boilerplate note that the loop manages the file:
        self.assertIn("loop will clear", prompt.lower())

    def test_no_hints_renders_fallback_block(self):
        prompt = build_plan_prompt(
            project_name="proj",
            project_path=self.root,
            state_dir=self.state,
            stage="prover",
            iter_num=7,
            captured_user_hints=None,
        )
        self.assertIn("No user hints this iteration", prompt)

    def test_doctor_findings_inline_in_prompt(self):
        # Write a prior-iter sidecar so the doctor block fires.
        prev = self.state / "logs" / "iter-006"
        prev.mkdir(parents=True)
        (prev / "blueprint-doctor.json").write_text(json.dumps({
            "orphan_chapters": ["/p/chapters/Stale.tex"],
            "broken_refs": [],
            "axiom_decls": [],
        }), encoding="utf-8")
        prompt = build_plan_prompt(
            project_name="proj",
            project_path=self.root,
            state_dir=self.state,
            stage="prover",
            iter_num=7,
        )
        self.assertIn("## Blueprint doctor", prompt)
        self.assertIn("Stale.tex", prompt)


class BuildDagPromptPhysicsTest(unittest.TestCase):
    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        self.state = self.root / ".archon"
        self.state.mkdir()
        (self.state / "subagents").mkdir()
        (self.state / "AGENTS.md").write_text("", encoding="utf-8")

    def tearDown(self):
        self._td.cleanup()

    def test_physics_mode_injects_typed_blueprint_policy(self):
        prompt = build_dag_prompt(
            project_name="physics_proj",
            project_path=self.root,
            state_dir=self.state,
            iter_num=1,
            physics_aware=True,
        )

        self.assertIn("## Physics-aware typed blueprint policy", prompt)
        self.assertIn("% archon:physics", prompt)
        self.assertIn("typed modeling nodes", prompt)
        self.assertIn("Symbols and image labels", prompt)
        self.assertIn("No unsupported scalar fallback", prompt)
        self.assertIn("physical-hypothesis nodes", prompt)
        self.assertIn("arbitrary field/force/motion", prompt)
        self.assertIn("governing physical assumptions", prompt)

    def test_default_dag_prompt_does_not_inject_physics_policy(self):
        prompt = build_dag_prompt(
            project_name="math_proj",
            project_path=self.root,
            state_dir=self.state,
            iter_num=1,
        )

        self.assertNotIn("## Physics-aware typed blueprint policy", prompt)
        self.assertNotIn("No unsupported scalar fallback", prompt)


class BuildReviewPromptPhysicsTest(unittest.TestCase):
    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        self.state = self.root / ".archon"
        self.state.mkdir()
        (self.state / "subagents").mkdir()
        chapter = self.root / "blueprint" / "src" / "chapters" / "Phys.tex"
        chapter.parent.mkdir(parents=True)
        chapter.write_text(
            "% archon:physics\n% archon:covers Phys.lean\n",
            encoding="utf-8",
        )

    def tearDown(self):
        self._td.cleanup()

    def test_physics_project_injects_review_checklist(self):
        prompt = build_review_prompt(
            project_name="physics_proj",
            project_path=self.root,
            state_dir=self.state,
            stage="autoformalize",
            session_num=1,
            session_dir=self.state / "proof-journal" / "sessions" / "session_001",
            attempts_file=self.state / "attempts.json",
            combined_prover_log=self.state / "logs" / "iter-001" / "prover.jsonl",
            iter_num=1,
        )

        self.assertIn("## Physics review requirements", prompt)
        self.assertIn("physics-reviewer", prompt)
        self.assertIn("LeanExplore grounding log", prompt)
        self.assertIn("Mathlib", prompt)
        self.assertIn("PhysLean", prompt)

    def test_physics_review_prompt_blocks_fake_statement_structures(self):
        prompt = build_review_prompt(
            project_name="physics_proj",
            project_path=self.root,
            state_dir=self.state,
            stage="autoformalize",
            session_num=1,
            session_dir=self.state / "proof-journal" / "sessions" / "session_001",
            attempts_file=self.state / "attempts.json",
            combined_prover_log=self.state / "logs" / "iter-001" / "prover.jsonl",
            iter_num=1,
        )

        self.assertIn("BLOCKER", prompt)
        self.assertIn("must not mark", prompt)
        self.assertIn("COMPLETE", prompt)
        self.assertIn("reviewer judgment", prompt)
        self.assertIn("physical-hypothesis completeness", prompt)
        self.assertIn("arbitrary field", prompt)
        self.assertIn("governing-law premise", prompt)
        self.assertIn("local approximations written as global", prompt)
        self.assertIn("tautological propositions", prompt)
        self.assertIn("disconnected", prompt)
        self.assertIn("HasDerivAt", prompt)
        self.assertIn("IsLittleO", prompt)
        self.assertIn("answer-as-assumption", prompt)
        self.assertIn("current target conclusion", prompt)
        self.assertIn("Valid...Physics", prompt)
        self.assertIn("Satisfies...", prompt)
        self.assertIn("derivability audit", prompt)
        self.assertIn("countermodel sanity check", prompt)
        self.assertIn("uncertainty/error propagation", prompt)
        self.assertIn("signed branches and orientation", prompt)
        self.assertIn("BLOCKED ON MODELING", prompt)

    def test_formalization_gate_requires_structured_semantic_certificate(self):
        prompt = build_review_prompt(
            project_name="physics_proj",
            project_path=self.root,
            state_dir=self.state,
            stage="autoformalize",
            session_num=1,
            session_dir=self.state / "proof-journal" / "sessions" / "session_001",
            attempts_file=self.state / "attempts.json",
            combined_prover_log=self.state / "logs" / "iter-001" / "prover.jsonl",
            iter_num=1,
            formalization_review_gate=True,
        )

        self.assertIn("Mandatory per-target formalization Review verdict", prompt)
        self.assertIn('"source_faithfulness"', prompt)
        self.assertIn('"derivability"', prompt)
        self.assertIn('"abstraction_sufficiency"', prompt)
        self.assertIn('"uncertainty_propagation"', prompt)
        self.assertIn('"branch_orientation"', prompt)
        self.assertIn('"countermodel_resistance"', prompt)
        self.assertIn('"bridge_obligations"', prompt)
        self.assertIn("legacy bare `passed` verdict", prompt)

    def test_proof_gate_requires_root_cause_routing_certificate(self):
        prompt = build_review_prompt(
            project_name="physics_proj",
            project_path=self.root,
            state_dir=self.state,
            stage="prover",
            session_num=2,
            session_dir=self.state / "proof-journal" / "sessions" / "session_002",
            attempts_file=self.state / "attempts.json",
            combined_prover_log=self.state / "logs" / "iter-002" / "prover.jsonl",
            iter_num=2,
            proof_review_gate=True,
        )

        self.assertIn("Mandatory per-target proof Review routing verdict", prompt)
        self.assertIn('"route": "solved|retry_proof|needs_redraft|blocked_infrastructure"', prompt)
        self.assertIn("underdetermined theorem/countermodel", prompt)
        self.assertIn("revoke the old", prompt)
        self.assertIn("missing", prompt)
        self.assertIn("mathematical bridge normally means `needs_redraft`", prompt)

    def test_non_physics_project_does_not_inject_review_checklist(self):
        (self.root / "blueprint" / "src" / "chapters" / "Phys.tex").write_text(
            "% ordinary chapter\n",
            encoding="utf-8",
        )

        prompt = build_review_prompt(
            project_name="math_proj",
            project_path=self.root,
            state_dir=self.state,
            stage="autoformalize",
            session_num=1,
            session_dir=self.state / "proof-journal" / "sessions" / "session_001",
            attempts_file=self.state / "attempts.json",
            combined_prover_log=self.state / "logs" / "iter-001" / "prover.jsonl",
            iter_num=1,
        )

        self.assertNotIn("## Physics review requirements", prompt)
        self.assertNotIn("LeanExplore grounding log", prompt)


if __name__ == "__main__":
    unittest.main()
