"""Tests for the sorryAx-laundering axiom sweep.

The sweep parses `check_axioms_inline.sh`'s human output, classifies
`sorryAx` dependencies as launderings, writes a report, and feeds the
launderings into the next plan prompt as open sorries.
"""

from __future__ import annotations

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
            scratch = root / ".archon" / "tmp" / "axiom-sweep"
            observed_probes: list[Path] = []

            def fake_run(command, **_kwargs):
                probe = Path(command[2])
                observed_probes.append(probe)
                self.assertNotEqual(probe.resolve(), source.resolve())
                self.assertEqual(probe.read_text(), original)
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
