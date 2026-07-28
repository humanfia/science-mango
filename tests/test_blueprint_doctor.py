"""Tests for the blueprint-doctor structural lint.

The doctor runs between prover and review each iter. It detects:
1. Orphan chapters — .tex files under blueprint/src/chapters/ not
   reachable from content.tex via \\input (directly or transitively).
2. Broken cross-references — \\ref{...} / \\uses{...} / \\cref{...}
   targets that no \\label{...} defines anywhere in the included tex
   tree.
Both are deterministic; the doctor never mutates the blueprint.
"""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from archon.commands.loop.blueprint_doctor import (
    _strip_tex_comments,
    run_blueprint_doctor,
    write_reports,
)


class StripTexCommentsTest(unittest.TestCase):
    def test_strips_basic_line_comment(self):
        self.assertEqual(
            _strip_tex_comments("alpha % comment text"),
            "alpha ",
        )

    def test_preserves_escaped_percent(self):
        self.assertEqual(
            _strip_tex_comments(r"50\% off % real comment"),
            r"50\% off ",
        )

    def test_strips_comment_at_line_start(self):
        self.assertEqual(
            _strip_tex_comments("% \\input{chapters/Orphan}\nactual line"),
            "\nactual line",
        )

    def test_preserves_lines_without_comments(self):
        text = "line1\nline2\nline3"
        self.assertEqual(_strip_tex_comments(text), text)


class _BlueprintProject:
    """Construct a temp project with a blueprint layout for the doctor.

    Default layout: content.tex \\inputs `macros/common` + `chapters/Good`;
    chapters/Orphan.tex exists but is not \\input'd (or is commented out).
    Good.tex has matching \\label / \\ref pairs; broken refs are
    added by the per-test caller via ``write_chapter``.
    """

    def __init__(self, root: Path):
        self.root = root
        self.src = root / "blueprint" / "src"
        self.chapters = self.src / "chapters"
        self.macros = self.src / "macros"
        self.chapters.mkdir(parents=True)
        self.macros.mkdir(parents=True)
        (self.macros / "common.tex").write_text("", encoding="utf-8")
        # Default content.tex with one included chapter and a commented-out
        # \\input for the orphan to exercise the comment stripper.
        (self.src / "content.tex").write_text(
            "\\input{macros/common}\n"
            "\\input{chapters/Good}\n"
            "% \\input{chapters/Orphan}\n",
            encoding="utf-8",
        )

    def write_chapter(self, name: str, body: str) -> Path:
        path = self.chapters / f"{name}.tex"
        path.write_text(body, encoding="utf-8")
        return path

    def include_chapter(self, name: str) -> None:
        content = (self.src / "content.tex").read_text(encoding="utf-8")
        content = content + f"\\input{{chapters/{name}}}\n"
        (self.src / "content.tex").write_text(content, encoding="utf-8")


class RunBlueprintDoctorTest(unittest.TestCase):
    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        self.bp = _BlueprintProject(self.root)

    def tearDown(self):
        self._td.cleanup()

    def test_returns_none_when_no_blueprint(self):
        # Empty dir — no blueprint/src/.
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(run_blueprint_doctor(Path(d)))

    def test_clean_project_has_no_findings(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}A.\\end{theorem}\n"
            "\\cref{thm:foo}\n",
        )
        # No Orphan.tex on disk → no orphans.
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertFalse(r.has_findings)
        self.assertEqual(r.orphan_chapters, [])
        self.assertEqual(r.broken_refs, [])

    def test_detects_literal_ref_placeholders(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}\n"
            "In the setting of Definition~REF, see Sections REF--REF.\n"
            "\\end{theorem}\n"
            "\\cref{thm:foo}\n",
        )
        r = run_blueprint_doctor(self.root)
        lits = [(k, reason) for _, k, reason in r.malformed_refs if k == "literal-ref"]
        self.assertEqual(len(lits), 3)
        self.assertIn("Definition~REF", lits[0][1])

    def test_no_literal_ref_false_positives(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:REF_like}\n"
            "PREFIX and REFEREE and \\cref{thm:REF_like} are fine.\n"
            "\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertEqual(
            [k for _, k, _ in r.malformed_refs if k == "literal-ref"], [],
        )

    def test_detects_interleaved_math_delimiters(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}\n"
            "Let $P \\subseteq Q\\( be the subsheaf whose \\)T$-points vanish.\n"
            "Then \\(H^1(C, \\mathcal{O}) = 0\\) and $x = y$.\n"
            "\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        probs = [reason for _, k, reason in r.malformed_refs if k == "math-delim"]
        self.assertTrue(any("inside $…$" in p for p in probs), probs)
        # The well-formed formulas on the next line produce no findings.
        self.assertTrue(all("line 3" not in p for p in probs), probs)

    def test_detects_bare_labels_in_prose(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}\\uses{lem:helper}\n"
            "By Kleiman Thm.~th:main the claim follows; see \\cref{thm:foo}.\n"
            "\\end{theorem}\n"
            "\\begin{lemma}\\label{lem:helper}H.\\end{lemma}\n",
        )
        r = run_blueprint_doctor(self.root)
        bare = [reason for _, k, reason in r.malformed_refs if k == "bare-label"]
        self.assertEqual(len(bare), 1, bare)
        self.assertIn("th:main", bare[0])
        # labels inside \uses{} / \cref{} / \label{} are never flagged.
        self.assertNotIn("lem:helper", " ".join(bare))
        self.assertNotIn("thm:foo", " ".join(bare))

    def test_detects_undefined_macros(self):
        # \Pic is defined in macros/common.tex; \fppf in-chapter; \mystery nowhere.
        (self.bp.macros / "common.tex").write_text(
            "\\DeclareMathOperator{\\Pic}{Pic}\n", encoding="utf-8",
        )
        self.bp.write_chapter(
            "Good",
            "\\providecommand{\\fppf}{\\mathrm{fppf}}\n"
            "\\begin{theorem}\\label{thm:foo}\n"
            "Then \\(\\Pic(C)_{\\fppf} \\to \\mystery(C)\\) is \\emph{flat}.\n"
            "\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        um = [reason for _, k, reason in r.malformed_refs if k == "undefined-macro"]
        self.assertEqual(len(um), 1, um)
        self.assertIn("\\mystery", um[0])

    def test_detects_orphan_chapter(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}A.\\end{theorem}\n",
        )
        self.bp.write_chapter(
            "Orphan",
            "\\begin{remark}Stuff.\\end{remark}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual(len(r.orphan_chapters), 1)
        self.assertEqual(r.orphan_chapters[0].name, "Orphan.tex")
        self.assertTrue(r.has_findings)

    def test_detects_broken_ref(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}A.\\end{theorem}\n"
            "\\ref{thm:nonexistent}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual(len(r.broken_refs), 1)
        chapter, kind, label = r.broken_refs[0]
        self.assertEqual(chapter.name, "Good.tex")
        self.assertEqual(kind, "ref")
        self.assertEqual(label, "thm:nonexistent")

    def test_detects_broken_uses_with_multiple_labels(self):
        # \uses{good, bad} — only ``bad`` is broken.
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:good}A.\\end{theorem}\n"
            "\\begin{theorem}\\label{thm:foo}\\uses{thm:good, thm:bad}B.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        labels = {label for _, _, label in r.broken_refs}
        self.assertEqual(labels, {"thm:bad"})

    def test_detects_empty_uses(self):
        # \uses{} — empty argument crashes plastex's depgraph builder.
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}\\uses{}A.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual(len(r.malformed_refs), 1)
        chapter, kind, reason = r.malformed_refs[0]
        self.assertEqual(chapter.name, "Good.tex")
        self.assertEqual(kind, "uses")
        self.assertEqual(reason, "empty argument")
        # Empty \uses{} must NOT bleed into broken_refs.
        self.assertEqual(r.broken_refs, [])
        self.assertTrue(r.has_findings)

    def test_detects_empty_proves(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}\\proves{}A.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        kinds = {k for _, k, _ in r.malformed_refs}
        self.assertIn("proves", kinds)

    def test_detects_empty_label(self):
        # \label{} — empty definition. Doesn't crash plastex on its own
        # but the depgraph treats the empty key as a self-cycle node.
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{}A.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        kinds_reasons = {(k, reason) for _, k, reason in r.malformed_refs}
        self.assertEqual(kinds_reasons, {("label", "empty argument")})

    def test_detects_empty_ref(self):
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:foo}A.\\end{theorem}\n"
            "\\ref{}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        kinds_reasons = {(k, reason) for _, k, reason in r.malformed_refs}
        self.assertEqual(kinds_reasons, {("ref", "empty argument")})

    def test_detects_empty_list_item_in_uses(self):
        # \uses{thm:good,,thm:other} — middle item is empty.
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:good}A.\\end{theorem}\n"
            "\\begin{theorem}\\label{thm:other}B.\\end{theorem}\n"
            "\\begin{theorem}\\label{thm:foo}"
            "\\uses{thm:good,,thm:other}C.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        # The non-empty pieces still resolve (no broken refs); the empty
        # piece in the middle is recorded as malformed.
        self.assertEqual(r.broken_refs, [])
        kinds_reasons = {(k, reason) for _, k, reason in r.malformed_refs}
        self.assertEqual(kinds_reasons, {("uses", "empty list item")})

    def test_detects_trailing_comma_in_uses(self):
        # \uses{thm:good,} — trailing comma yields one empty list item.
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:good}A.\\end{theorem}\n"
            "\\begin{theorem}\\label{thm:foo}"
            "\\uses{thm:good,}B.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual(r.broken_refs, [])
        kinds_reasons = {(k, reason) for _, k, reason in r.malformed_refs}
        self.assertEqual(kinds_reasons, {("uses", "empty list item")})

    def test_ignores_commented_input(self):
        # The default content.tex has a commented-out \\input for Orphan;
        # the comment-stripping should keep Orphan.tex marked orphan.
        self.bp.write_chapter("Good", "\\label{thm:foo}\n")
        self.bp.write_chapter("Orphan", "\\label{thm:bar}\n")
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual([p.name for p in r.orphan_chapters], ["Orphan.tex"])

    def test_detects_axiom_declaration(self):
        self.bp.write_chapter("Good", "\\label{thm:foo}\n")
        # An axiom under the project's .lean files.
        (self.root / "Foo.lean").write_text(
            "axiom magic_axiom : True\n", encoding="utf-8",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual(len(r.axiom_decls), 1)
        path, name = r.axiom_decls[0]
        self.assertEqual(path.name, "Foo.lean")
        self.assertEqual(name, "magic_axiom")

    def test_axiom_in_comment_not_flagged(self):
        self.bp.write_chapter("Good", "\\label{thm:foo}\n")
        (self.root / "Foo.lean").write_text(
            "-- axiom foo : True (this is a NOTE, not a real axiom)\n"
            "/- axiom bar : True -/\n"
            "theorem real_theorem : True := trivial\n",
            encoding="utf-8",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual(r.axiom_decls, [])

    def test_axiom_under_lake_excluded(self):
        self.bp.write_chapter("Good", "\\label{thm:foo}\n")
        # Real .lean in project — clean.
        (self.root / "Project.lean").write_text(
            "theorem t : True := trivial\n", encoding="utf-8",
        )
        # Axiom under .lake/ — must be ignored (dep code).
        lake = self.root / ".lake" / "packages" / "mathlib"
        lake.mkdir(parents=True)
        (lake / "Foo.lean").write_text(
            "axiom dep_axiom : True\n", encoding="utf-8",
        )
        # Axiom under .archon/ — must be ignored (snapshots).
        snap = self.root / ".archon" / "logs" / "iter-001" / "snapshots"
        snap.mkdir(parents=True)
        (snap / "Foo.lean").write_text(
            "axiom snapshot_axiom : True\n", encoding="utf-8",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        self.assertEqual(r.axiom_decls, [])

    def test_physics_mode_flags_scalar_quantity_fallbacks(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers Phys.lean\n"
            "\\begin{definition}\\label{def:charge_type}\\lean{Phys.Charge}\n"
            "Electric charge is a typed quantity in the local model.\n"
            "\\end{definition}\n",
        )
        (self.root / "Phys.lean").write_text(
            "abbrev Charge := ℝ\n"
            "abbrev Force := Real\n"
            "abbrev Radius := ℝ\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        self.assertIsNotNone(r)
        reasons = [reason for _, _, reason in r.physics_modeling_problems]
        self.assertTrue(any("Charge" in reason for reason in reasons), reasons)
        self.assertTrue(any("Force" in reason for reason in reasons), reasons)
        self.assertTrue(any("Radius" in reason for reason in reasons), reasons)
        self.assertTrue(r.has_findings)

    def test_physics_mode_flags_existential_only_load_bearing_predicate(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n% archon:covers Phys.lean\n",
        )
        (self.root / "Phys.lean").write_text(
            "import Mathlib\n"
            "import Physlib\n"
            "structure Setup where\n"
            "  radiusAtIncidence : ℝ → ℝ\n"
            "  isTangentToContainer : Nat → ℝ → Prop\n"
            "structure Laws (setup : Setup) : Prop where\n"
            "  limiting_path_exists :\n"
            "    ∀ theta, ∃ path, setup.isTangentToContainer path "
            "(setup.radiusAtIncidence theta)\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        findings = [
            reason for _, kind, reason in r.physics_modeling_problems
            if kind == "opaque-existential-physics-relation"
        ]
        self.assertEqual(len(findings), 1)
        self.assertIn("isTangentToContainer", findings[0])

    def test_physics_mode_accepts_opaque_relation_with_eliminator_law(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n% archon:covers Phys.lean\n",
        )
        (self.root / "Phys.lean").write_text(
            "import Mathlib\n"
            "import Physlib\n"
            "structure Setup where\n"
            "  radiusAtIncidence : ℝ → ℝ\n"
            "  isTangentToContainer : Nat → ℝ → Prop\n"
            "structure Laws (setup : Setup) : Prop where\n"
            "  limiting_path_exists :\n"
            "    ∀ theta, ∃ path, setup.isTangentToContainer path "
            "(setup.radiusAtIncidence theta)\n"
            "  tangent_radius_equation :\n"
            "    ∀ path radius, setup.isTangentToContainer path radius → "
            "radius = 1\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        kinds = {kind for _, kind, _ in r.physics_modeling_problems}
        self.assertNotIn("opaque-existential-physics-relation", kinds)

    def test_physics_mode_flags_unpropagated_uncertainty(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n% archon:covers Phys.lean\n",
        )
        (self.root / "Phys.lean").write_text(
            "import Mathlib\n"
            "import Physlib\n"
            "structure Estimate where\n"
            "  centralValue : ℝ\n"
            "  uncertaintyValue : ℝ\n"
            "  uncertainty_nonnegative : 0 ≤ uncertaintyValue\n"
            "structure Previous (estimate : Estimate) : Prop where\n"
            "  uncertainty_readout : estimate.uncertaintyValue = 2\n"
            "theorem target (estimate : Estimate) (_previous : Previous estimate) :\n"
            "    |estimate.centralValue - 10| ≤ 2 := by\n"
            "  sorry\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        findings = [
            reason for _, kind, reason in r.physics_modeling_problems
            if kind == "unpropagated-uncertainty"
        ]
        self.assertEqual(len(findings), 1)
        self.assertIn("uncertaintyValue", findings[0])

    def test_physics_mode_accepts_uncertainty_in_target_contract(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n% archon:covers Phys.lean\n",
        )
        (self.root / "Phys.lean").write_text(
            "import Mathlib\n"
            "import Physlib\n"
            "structure Estimate where\n"
            "  centralValue : ℝ\n"
            "  uncertaintyValue : ℝ\n"
            "  uncertainty_nonnegative : 0 ≤ uncertaintyValue\n"
            "structure Previous (estimate : Estimate) : Prop where\n"
            "  uncertainty_readout : estimate.uncertaintyValue = 2\n"
            "theorem target (estimate : Estimate) (_previous : Previous estimate) :\n"
            "    |estimate.centralValue - 10| ≤ estimate.uncertaintyValue := by\n"
            "  sorry\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        kinds = {kind for _, kind, _ in r.physics_modeling_problems}
        self.assertNotIn("unpropagated-uncertainty", kinds)

    def test_physics_mode_flags_missing_grounding_log_for_existing_target(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers Phys.lean\n"
            "\\begin{definition}\\label{def:charge_type}\\lean{Phys.Charge}\n"
            "Electric charge is a typed quantity in the local model.\n"
            "\\end{definition}\n",
        )
        (self.root / "Phys.lean").write_text(
            "theorem target : True := by sorry\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        self.assertIsNotNone(r)
        reasons = [reason for _, _, reason in r.physics_grounding_problems]
        self.assertTrue(any("Phys.lean" in reason for reason in reasons), reasons)
        self.assertTrue(any("LeanExplore" in reason for reason in reasons), reasons)
        self.assertTrue(r.has_findings)

    def test_physics_mode_accepts_complete_grounding_log(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers Phys.lean\n",
        )
        (self.root / "Phys.lean").write_text(
            "theorem target : True := by sorry\n",
            encoding="utf-8",
        )
        tr = self.root / ".archon" / "task_results"
        tr.mkdir(parents=True)
        (tr / "Phys.lean.md").write_text(
            "# Phys.lean task result\n\n"
            "## LeanExplore queries/candidates actually used\n"
            "- query: electric charge, packages: Mathlib, PhysLean\n"
            "- candidate: PhysLean.Electromagnetism.Charge\n\n"
            "## PhysLean/Mathlib names grounded\n"
            "- PhysLean.Electromagnetism.Charge\n\n"
            "## Local abstractions introduced\n"
            "- none\n\n"
            "## Grounding gaps\n"
            "- none\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        self.assertIsNotNone(r)
        self.assertEqual(r.physics_grounding_problems, [])

    def test_physics_mode_rejects_incomplete_grounding_log(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers Phys.lean\n",
        )
        (self.root / "Phys.lean").write_text(
            "theorem target : True := by sorry\n",
            encoding="utf-8",
        )
        tr = self.root / ".archon" / "task_results"
        tr.mkdir(parents=True)
        (tr / "Phys.lean.md").write_text(
            "# Physics LeanExplore Grounding Log\n\n"
            "- Grounding status: incomplete\n"
            "- Packages searched: Mathlib, PhysLean\n\n"
            "## LeanExplore queries/candidates actually used\n"
            "- ERROR: LEANEXPLORE_API_KEY is missing; no searcher available.\n\n"
            "## Grounded Mathlib/PhysLean names\n"
            "- None yet.\n\n"
            "## Local abstractions introduced\n"
            "- none\n\n"
            "## Grounding gaps\n"
            "- LEANEXPLORE_API_KEY is missing.\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        self.assertIsNotNone(r)
        reasons = [reason for _, _, reason in r.physics_grounding_problems]
        self.assertTrue(any("successful LeanExplore search" in reason for reason in reasons), reasons)

    def test_non_physics_project_allows_scalar_abbrevs(self):
        self.bp.write_chapter("Good", "\\label{thm:foo}\n")
        (self.root / "Project.lean").write_text(
            "abbrev Charge := ℝ\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        self.assertIsNotNone(r)
        self.assertEqual(r.physics_modeling_problems, [])

    def test_label_in_included_subfile_is_reachable(self):
        # When chapters \\input each other, labels in the leaf chapter
        # must still satisfy refs in the parent chapter (transitive
        # inclusion).
        self.bp.write_chapter(
            "Good",
            "\\input{chapters/Leaf}\n\\ref{thm:in_leaf}\n",
        )
        self.bp.write_chapter(
            "Leaf",
            "\\begin{theorem}\\label{thm:in_leaf}A.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        self.assertIsNotNone(r)
        # Leaf is transitively included from Good (which is in content.tex),
        # so it should NOT count as orphan; ref should resolve.
        orphan_names = [p.name for p in r.orphan_chapters]
        self.assertNotIn("Leaf.tex", orphan_names)
        self.assertEqual(r.broken_refs, [])


class WriteReportsTest(unittest.TestCase):
    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        self.bp = _BlueprintProject(self.root)

    def tearDown(self):
        self._td.cleanup()

    def test_clean_report_emits_short_message(self):
        self.bp.write_chapter("Good", "\\label{thm:foo}\n")
        r = run_blueprint_doctor(self.root)
        iter_dir = self.root / ".archon" / "logs" / "iter-001"
        json_path, md_path = write_reports(r, iter_dir, self.root)
        self.assertTrue(json_path.is_file())
        self.assertTrue(md_path.is_file())
        md = md_path.read_text(encoding="utf-8")
        self.assertIn("No structural findings", md)

    def test_findings_report_lists_orphans_and_refs(self):
        self.bp.write_chapter(
            "Good",
            "\\label{thm:foo}\n\\ref{thm:broken}\n",
        )
        self.bp.write_chapter("Orphan", "stuff\n")
        r = run_blueprint_doctor(self.root)
        iter_dir = self.root / ".archon" / "logs" / "iter-002"
        json_path, md_path = write_reports(r, iter_dir, self.root)
        md = md_path.read_text(encoding="utf-8")
        self.assertIn("## Orphan chapters", md)
        self.assertIn("Orphan.tex", md)
        self.assertIn("## Broken cross-references", md)
        self.assertIn("thm:broken", md)
        # JSON sidecar parses.
        import json
        data = json.loads(json_path.read_text(encoding="utf-8"))
        self.assertEqual(len(data["orphan_chapters"]), 1)
        self.assertEqual(len(data["broken_refs"]), 1)

    def test_findings_report_lists_malformed_annotations(self):
        # Mix of empty argument and empty list item — both must surface
        # in the Markdown report and the JSON sidecar.
        self.bp.write_chapter(
            "Good",
            "\\begin{theorem}\\label{thm:good}A.\\end{theorem}\n"
            "\\begin{theorem}\\label{thm:other}B.\\end{theorem}\n"
            "\\begin{theorem}\\label{thm:foo}"
            "\\uses{}\\uses{thm:good,,thm:other}C.\\end{theorem}\n",
        )
        r = run_blueprint_doctor(self.root)
        iter_dir = self.root / ".archon" / "logs" / "iter-003"
        json_path, md_path = write_reports(r, iter_dir, self.root)
        md = md_path.read_text(encoding="utf-8")
        self.assertIn("## Malformed annotations", md)
        self.assertIn("empty argument", md)
        self.assertIn("empty list item", md)
        import json
        data = json.loads(json_path.read_text(encoding="utf-8"))
        self.assertEqual(len(data["malformed_refs"]), 2)
        reasons = {entry["reason"] for entry in data["malformed_refs"]}
        self.assertEqual(reasons, {"empty argument", "empty list item"})

    def test_findings_report_lists_physics_modeling_problems(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n\\label{thm:foo}\n",
        )
        (self.root / "Phys.lean").write_text(
            "abbrev ElectricCharge := ℝ\n",
            encoding="utf-8",
        )
        r = run_blueprint_doctor(self.root)
        iter_dir = self.root / ".archon" / "logs" / "iter-004"
        json_path, md_path = write_reports(r, iter_dir, self.root)
        md = md_path.read_text(encoding="utf-8")
        self.assertIn("## Physics modeling", md)
        self.assertIn("ElectricCharge", md)
        import json
        data = json.loads(json_path.read_text(encoding="utf-8"))
        self.assertEqual(len(data["physics_modeling_problems"]), 1)

    def test_flags_self_contained_physics_target_without_real_imports(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers Bad.lean\n"
            "\\label{thm:foo}\n",
        )
        (self.root / "Bad.lean").write_text(
            "/- intentionally self-contained smoke-test file: "
            "does not expose PhysLean/Mathlib -/\n"
            "class PhysicsScalar (α : Type u) extends Zero α where\n"
            "  fromNat : Nat → α\n"
            "inductive Dimension where\n"
            "  | length\n"
            "structure Quantity (α : Type u) (dim : Dimension) where\n"
            "  scalar : α\n"
            "def PositiveScalar (a : α) : Prop := True\n"
            "inductive TaylorOrder where\n"
            "  | linear\n"
            "structure CartesianFieldJacobian (α : Type u) where\n"
            "  dEx_dx : α\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        kinds = {kind for _, kind, _ in r.physics_modeling_problems}
        self.assertIn("missing-mathlib-import", kinds)
        self.assertIn("missing-physlib-import", kinds)
        self.assertIn("self-contained-physics-file", kinds)
        self.assertIn("physics-scalar-class", kinds)
        self.assertIn("local-dimension-tags", kinds)
        self.assertIn("symbolic-positivity-tag", kinds)
        self.assertIn("asymptotic-tag-fallback", kinds)
        self.assertIn("jacobian-record-fallback", kinds)

    def test_physlean_coverage_exemption_suppresses_only_domain_import(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers Exempt.lean\n"
            "% NOTE: PhysLean-coverage exemption: no matching domain module.\n"
            "\\label{thm:foo}\n",
        )
        (self.root / "Exempt.lean").write_text(
            "import Mathlib\n"
            "theorem foo : True := by trivial\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        kinds = {kind for _, kind, _ in r.physics_modeling_problems}
        self.assertNotIn("missing-physlib-import", kinds)
        self.assertNotIn("missing-mathlib-import", kinds)

    def test_physlean_coverage_exemption_does_not_hide_mathlib_requirement(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers Exempt.lean\n"
            "% NOTE: PhysLean-coverage exemption: no matching domain module.\n"
            "\\label{thm:foo}\n",
        )
        (self.root / "Exempt.lean").write_text(
            "theorem foo : True := by trivial\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        kinds = {kind for _, kind, _ in r.physics_modeling_problems}
        self.assertNotIn("missing-physlib-import", kinds)
        self.assertIn("missing-mathlib-import", kinds)

    def test_does_not_hardcode_fake_physics_statement_semantics(self):
        self.bp.write_chapter(
            "Good",
            "% archon:physics\n"
            "% archon:covers FakeStatement.lean\n"
            "\\label{thm:foo}\n",
        )
        (self.root / "FakeStatement.lean").write_text(
            "import Mathlib\n"
            "import Physlib.Electromagnetism.Basic\n"
            "structure FieldComponentProjection where\n"
            "  E_x : ℝ → ℝ\n"
            "  E_y : ℝ → ℝ\n"
            "  E_z : ℝ → ℝ\n"
            "def firstOrderElectricFieldFormula (field : FieldComponentProjection) : Prop :=\n"
            "  ∀ x y z : ℝ, field.E_x x = -x ∧ field.E_y y = -y ∧ field.E_z z = z\n"
            "def transverseSymmetry (field : FieldComponentProjection) : Prop :=\n"
            "  ∃ _transverse : ℝ, True\n"
            "def sourceFreeTraceCondition (_field : FieldComponentProjection) : Prop :=\n"
            "  ∃ transverse axial : ℝ, axial = 1 ∧ 2 * transverse + axial = 0\n",
            encoding="utf-8",
        )

        r = run_blueprint_doctor(self.root)

        kinds = {kind for _, kind, _ in r.physics_modeling_problems}
        self.assertNotIn("linearization-as-global-equality", kinds)
        self.assertNotIn("tautological-exists-true", kinds)
        self.assertNotIn("disconnected-calculus-statement", kinds)


if __name__ == "__main__":
    unittest.main()
