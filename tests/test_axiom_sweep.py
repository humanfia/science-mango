"""Tests for the sorryAx-laundering axiom sweep.

The sweep parses `check_axioms_inline.sh`'s human output, classifies
`sorryAx` dependencies as launderings, writes a report, and feeds the
launderings into the next plan prompt as open sorries.
"""

from __future__ import annotations

import os
import subprocess
import tempfile
import threading
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from archon.commands.loop.axiom_sweep import (
    AxiomFinding,
    AxiomSweepReport,
    _AxiomFileResult,
    _ANSI_RE,
    _FINDING_RE,
    _project_lean_files,
    run_axiom_sweep,
    write_reports,
)
from archon.prompts import _axiom_sweep_findings_block


_CHECK_AXIOMS_SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "src"
    / "archon"
    / ".archon-src"
    / "skills"
    / "lean4"
    / "lib"
    / "scripts"
    / "check_axioms_inline.sh"
)


class CleanupSafetyTest(unittest.TestCase):
    def test_backup_restore_is_explicitly_noninteractive(self):
        script = _CHECK_AXIOMS_SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'mv -f -- "$original.axiom_check_backup" "$original"',
            script,
        )
        self.assertIn('mv -f -- "$BACKUP_FILE" "$FILE"', script)
        self.assertNotIn(
            'mv "$original.axiom_check_backup" "$original"',
            script,
        )
        self.assertNotIn('mv "$BACKUP_FILE" "$FILE"', script)


class FindingParseTest(unittest.TestCase):
    def test_parses_decls_and_strips_ansi(self):
        raw = (
            "\x1b[0;34mFile: \x1b[1;33mFoo.lean\x1b[0m\n"
            "  \x1b[0;31m⚠ Foo.bar uses non-standard axiom: sorryAx\x1b[0m\n"
            "  ⚠ Foo.baz uses non-standard axiom: myAxiom\n"
        )
        clean = _ANSI_RE.sub("", raw)
        found = [
            AxiomFinding(m.group("decl"), m.group("axiom"))
            for m in _FINDING_RE.finditer(clean)
        ]
        self.assertEqual([f.decl for f in found], ["Foo.bar", "Foo.baz"])
        self.assertTrue(found[0].is_sorry)
        self.assertFalse(found[1].is_sorry)


class DeclarationExtractionRegressionTest(unittest.TestCase):
    """End-to-end regressions for checker declaration discovery."""

    def _printed_declarations_from_source(self, source_text: str) -> list[str]:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            source = root / "Regression.lean"
            source.write_text(source_text, encoding="utf-8")
            capture = root / "printed.txt"
            fake_bin = root / "bin"
            fake_bin.mkdir()
            fake_lake = fake_bin / "lake"
            fake_lake.write_text(
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                "probe=${3:?missing Lean probe}\n"
                "awk '\n"
                "  /AUTO_AXIOM_CHECK_MARKER_DO_NOT_COMMIT/ { active = 1; next }\n"
                "  active && /^#print axioms / { print }\n"
                "' \"$probe\" > \"$AXIOM_CAPTURE\"\n",
                encoding="utf-8",
            )
            fake_lake.chmod(0o755)
            env = os.environ.copy()
            env["PATH"] = f"{fake_bin}{os.pathsep}{env.get('PATH', '')}"
            env["AXIOM_CAPTURE"] = str(capture)

            result = subprocess.run(
                ["bash", str(_CHECK_AXIOMS_SCRIPT), str(source), "--report-only"],
                cwd=root,
                capture_output=True,
                text=True,
                env=env,
                timeout=10,
            )

            self.assertEqual(
                result.returncode,
                0,
                msg=f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
            )
            self.assertEqual(
                source.read_text(encoding="utf-8"),
                source_text,
            )
            return capture.read_text(encoding="utf-8").splitlines()

    def _printed_declarations(self, false_failure_fragment: str) -> list[str]:
        return self._printed_declarations_from_source(
            "namespace Regression\n"
            "def kept : True := True\n"
            "instance keptInstance : Inhabited Unit := ⟨()⟩\n"
            "structure KeptStructure where\n"
            "  value : Nat\n"
            f"{false_failure_fragment}\n"
            "end Regression\n"
        )

    def test_k3_iter_001_false_failure_patterns_are_not_declarations(self):
        cases = {
            "t5_a1_parameterized_anonymous_instance": (
                "instance (n : ℕ) : Fintype (OpenEnd n) := inferInstance"
            ),
            "t5_a3_anonymous_example": (
                "example : pl1TotalBonds 17 31 = 255 := by norm_num"
            ),
            "t9_a1_module_doc_structure_prose": (
                "/-!\n"
                "The page figure labels the cyclic\n"
                "structure \"n = 7, β-CD\" and counts its substituents.\n"
                "-/"
            ),
            "t9_a3_colon_anonymous_instance": (
                "instance : BEq PrecursorAtom := "
                "⟨fun a b => a.1 == b.1⟩"
            ),
            "t9_a7_declaration_doc_structure_prose": (
                "/-- The cyclic positions form a ring; the ring\n"
                "structure makes `ZMod 7` the natural carrier. -/"
            ),
        }
        expected = [
            "#print axioms Regression.kept",
            "#print axioms Regression.keptInstance",
            "#print axioms Regression.KeptStructure",
        ]
        for name, fragment in cases.items():
            with self.subTest(name=name):
                self.assertEqual(self._printed_declarations(fragment), expected)

    def test_nested_namespace_stack_qualifies_inner_and_outer_declarations(self):
        source = (
            "namespace Icho2026T6A7\n"
            "def piElectrons : Nat := 14\n"
            "namespace PathwayPiFeature\n"
            "def piElectrons : Nat := 2\n"
            "namespace Deep.Tools\n"
            "theorem counted : True := by trivial\n"
            "end Deep.Tools\n"
            "end PathwayPiFeature\n"
            "namespace PorphyrinNanoring\n"
            "def piElectrons : Nat := 84\n"
            "end PorphyrinNanoring\n"
            "lemma outerAgain : True := by trivial\n"
            "end Icho2026T6A7\n"
            "def rootDeclaration : Nat := 0\n"
        )

        self.assertEqual(
            self._printed_declarations_from_source(source),
            [
                "#print axioms Icho2026T6A7.piElectrons",
                "#print axioms Icho2026T6A7.PathwayPiFeature.piElectrons",
                "#print axioms "
                "Icho2026T6A7.PathwayPiFeature.Deep.Tools.counted",
                "#print axioms Icho2026T6A7.PorphyrinNanoring.piElectrons",
                "#print axioms Icho2026T6A7.outerAgain",
                "#print axioms rootDeclaration",
            ],
        )

    def test_bare_and_named_ends_preserve_the_remaining_namespace_stack(self):
        source = (
            "namespace Outer\n"
            "section LocalFacts\n"
            "def insideSection : Nat := 1\n"
            "namespace Inner\n"
            "def nested : Nat := 2\n"
            "end\n"
            "def afterBareEnd : Nat := 3\n"
            "end LocalFacts\n"
            "def afterNamedSectionEnd : Nat := 4\n"
            "namespace Final\n"
            "def lastNested : Nat := 5\n"
            "end Final\n"
            "end Outer\n"
        )

        self.assertEqual(
            self._printed_declarations_from_source(source),
            [
                "#print axioms Outer.insideSection",
                "#print axioms Outer.Inner.nested",
                "#print axioms Outer.afterBareEnd",
                "#print axioms Outer.afterNamedSectionEnd",
                "#print axioms Outer.Final.lastNested",
            ],
        )

    def test_comments_and_string_delimiters_do_not_change_namespace_stack(self):
        source = (
            "namespace Visible\n"
            "def before : Nat := 1\n"
            "/- namespace Fake\n"
            "def hidden : Nat := 0\n"
            "/- end Fake -/\n"
            "end Fake -/\n"
            'def literal : String := "/- not a comment; -- still a string"\n'
            "namespace Nested\n"
            "def after : Nat := 2\n"
            "end Nested\n"
            "end Visible\n"
        )

        self.assertEqual(
            self._printed_declarations_from_source(source),
            [
                "#print axioms Visible.before",
                "#print axioms Visible.literal",
                "#print axioms Visible.Nested.after",
            ],
        )


class ReportTest(unittest.TestCase):
    def test_only_sorry_findings_are_launderings(self):
        rep = AxiomSweepReport(
            findings=[AxiomFinding("A.b", "sorryAx"), AxiomFinding("A.c", "myAx")],
            ran=True,
        )
        self.assertEqual([f.decl for f in rep.sorry_launderings], ["A.b"])
        self.assertEqual([f.decl for f in rep.other_axioms], ["A.c"])
        self.assertTrue(rep.has_launderings)

class ParallelSweepTest(unittest.TestCase):
    def test_full_scan_excludes_hidden_runtime_copies(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            visible = root / "Problems" / "A.lean"
            runtime = root / ".archon" / "logs" / "iter-001" / "A.lean"
            lake_cache = root / ".lake" / "build" / "B.lean"
            for path in (visible, runtime, lake_cache):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("theorem x : True := by trivial\n")

            self.assertEqual(_project_lean_files(root), [visible.resolve()])

    def test_checker_runs_on_disposable_copy_and_preserves_source(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.lean").write_text("package test\n")
            source = root / "A.lean"
            original = "theorem a : True := by trivial\n"
            source.write_text(original)
            source.chmod(0o444)
            scratch = root / ".archon" / "tmp" / "axiom-sweep"
            observed_probes: list[Path] = []

            def fake_run(command, **_kwargs):
                probe = Path(command[2])
                observed_probes.append(probe)
                self.assertNotEqual(probe.resolve(), source.resolve())
                self.assertEqual(probe.read_text(), original)
                self.assertTrue(probe.stat().st_mode & 0o200)
                self.assertIs(_kwargs.get("stdin"), subprocess.DEVNULL)
                probe.write_text("mutated disposable probe\n")
                return SimpleNamespace(
                    returncode=0,
                    stdout=(
                        f"File: {probe}\n"
                        "  ⚠ A.a uses non-standard axiom: sorryAx\n"
                    ),
                    stderr="",
                )

            with patch(
                "archon.commands.loop.axiom_sweep.subprocess.run",
                side_effect=fake_run,
            ):
                report = run_axiom_sweep(
                    root,
                    targets=[source],
                    jobs=1,
                    scratch_root=scratch,
                )

            self.assertIsNotNone(report)
            self.assertTrue(report.ran)
            self.assertEqual(source.read_text(), original)
            self.assertEqual(source.stat().st_mode & 0o777, 0o444)
            self.assertEqual(report.target_files, ["A.lean"])
            self.assertEqual(report.findings[0].file, "A.lean")
            self.assertTrue(report.findings[0].is_sorry)
            self.assertFalse(observed_probes[0].exists())

    def test_target_checks_run_concurrently_with_stable_aggregation(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.lean").write_text("package test\n")
            scratch = root / ".archon" / "tmp" / "axiom-sweep"
            objectives = []
            for name in ("D", "B", "A", "C"):
                target = root / f"{name}.lean"
                target.write_text(f"theorem {name.lower()} : True := by trivial\n")
                objectives.append(target)

            lock = threading.Lock()
            active = 0
            peak = 0

            def fake_worker(*, project_path, source, **_kwargs):
                nonlocal active, peak
                with lock:
                    active += 1
                    peak = max(peak, active)
                time.sleep(0.03)
                with lock:
                    active -= 1
                rel = source.relative_to(project_path).as_posix()
                return _AxiomFileResult(
                    rel=rel,
                    findings=(AxiomFinding(rel, "myAxiom", rel),),
                    files_checked=1,
                )

            report = run_axiom_sweep(
                root,
                targets=objectives,
                jobs=4,
                scratch_root=scratch,
                worker_fn=fake_worker,
                executor_factory=ThreadPoolExecutor,
            )

            self.assertTrue(report.ran)
            self.assertGreaterEqual(peak, 2)
            self.assertEqual(report.jobs, 4)
            self.assertEqual(
                report.target_files,
                ["A.lean", "B.lean", "C.lean", "D.lean"],
            )
            self.assertEqual(
                [finding.file for finding in report.findings],
                report.target_files,
            )



class PlanInjectionTest(unittest.TestCase):
    def _state_with_report(self, rep: AxiomSweepReport) -> Path:
        d = tempfile.mkdtemp()
        state = Path(d)
        self.addCleanup(lambda: __import__("shutil").rmtree(d, ignore_errors=True))
        iterlog = state / "logs" / "iter-002"
        iterlog.mkdir(parents=True)
        write_reports(rep, iterlog, state)
        return state

    def test_launderings_injected_for_next_iter(self):
        state = self._state_with_report(
            AxiomSweepReport(findings=[AxiomFinding("A.b", "sorryAx")], ran=True)
        )
        block = _axiom_sweep_findings_block(state, 3)  # iter 3 reads iter-002
        self.assertIn("sorryAx laundering", block)
        self.assertIn("A.b", block)

    def test_no_launderings_is_empty_block(self):
        state = self._state_with_report(
            AxiomSweepReport(findings=[AxiomFinding("A.c", "myAx")], ran=True)
        )
        self.assertEqual(_axiom_sweep_findings_block(state, 3), "")

    def test_iter_one_is_empty(self):
        state = self._state_with_report(
            AxiomSweepReport(findings=[AxiomFinding("A.b", "sorryAx")], ran=True)
        )
        self.assertEqual(_axiom_sweep_findings_block(state, 1), "")


if __name__ == "__main__":
    unittest.main()
