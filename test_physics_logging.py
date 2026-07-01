"""Tests for physics formalizer diagnostic logging."""

from __future__ import annotations

import importlib
import logging
import sys
import tempfile
import threading
import unittest
from pathlib import Path


FORMALIZER_DIR = (
    Path(__file__).resolve().parents[1]
    / "src"
    / "archon"
    / "formalizer"
    / "Formalizer"
)


class FormalizerImportMixin:
    def setUp(self):
        self._old_path = list(sys.path)
        self._old_modules = {
            name: module
            for name, module in sys.modules.items()
            if name == "config" or name.startswith("modules")
        }
        for name in list(self._old_modules):
            sys.modules.pop(name, None)
        sys.path.insert(0, str(FORMALIZER_DIR))

    def tearDown(self):
        sys.path[:] = self._old_path
        for name in list(sys.modules):
            if name == "config" or name.startswith("modules"):
                sys.modules.pop(name, None)
        sys.modules.update(self._old_modules)


class PhysicsLoggingTests(FormalizerImportMixin, unittest.TestCase):
    def test_task_logger_records_stage2_worker_threads_for_same_problem(self):
        logger_setup = importlib.import_module("modules.logger_setup")
        logger = logging.getLogger()
        old_handlers = list(logger.handlers)
        old_level = logger.level
        logger.handlers.clear()
        logger.setLevel(logging.DEBUG)

        with tempfile.TemporaryDirectory() as tmpdir:
            log_path = Path(tmpdir) / "problem_p1.log"
            threading.current_thread().name = "Thread-Pp1"
            handler = logger_setup.setup_task_logger(str(log_path))
            try:
                logging.info("main-thread-visible")

                def worker_log():
                    threading.current_thread().name = "Thread-Pp1-w0"
                    logging.debug("stage2-worker-visible")

                worker = threading.Thread(target=worker_log)
                worker.start()
                worker.join()
            finally:
                logger_setup.close_task_logger(handler)
                logger.handlers[:] = old_handlers
                logger.setLevel(old_level)

            text = log_path.read_text(encoding="utf-8")

        self.assertIn("main-thread-visible", text)
        self.assertIn("stage2-worker-visible", text)

    def test_main_thread_task_logger_records_stage2_worker_threads(self):
        logger_setup = importlib.import_module("modules.logger_setup")
        logger = logging.getLogger()
        old_handlers = list(logger.handlers)
        old_level = logger.level
        logger.handlers.clear()
        logger.setLevel(logging.DEBUG)

        with tempfile.TemporaryDirectory() as tmpdir:
            log_path = Path(tmpdir) / "problem_p1.log"
            threading.current_thread().name = "MainThread"
            handler = logger_setup.setup_task_logger(str(log_path))
            try:
                logging.info("main-thread-visible")

                def worker_log():
                    threading.current_thread().name = "Thread-Pp1-stage2-w0"
                    logging.warning("stage2-worker-visible")

                worker = threading.Thread(target=worker_log)
                worker.start()
                worker.join()
            finally:
                logger_setup.close_task_logger(handler)
                logger.handlers[:] = old_handlers
                logger.setLevel(old_level)

            text = log_path.read_text(encoding="utf-8")

        self.assertIn("main-thread-visible", text)
        self.assertIn("stage2-worker-visible", text)

    def test_stage2_worker_writes_candidate_and_error_artifacts(self):
        config = importlib.import_module("config")
        config.ATTEMPTS_PER_WORKER = 1
        config.CURRENT_DOMAIN = "physics"
        config.PHYSICS_STUB_FALLBACK = False
        stage2 = importlib.import_module("stage2_synthesizer")

        class FakeLLM:
            def run_synthesis_module(self, *_args, **_kwargs):
                return "def BadCharge : MissingType := by sorry"

        class FakeCompiler:
            def compile_code(self, *_args, **_kwargs):
                return type(
                    "CompileResult",
                    (),
                    {
                        "status": "failure",
                        "error_message": "unknown identifier 'MissingType'",
                    },
                )()

        synth = stage2.GoTSynthesizer.__new__(stage2.GoTSynthesizer)
        synth.llm = FakeLLM()
        synth.compiler = FakeCompiler()

        with tempfile.TemporaryDirectory() as tmpdir:
            synth.debug_dir = tmpdir
            result = synth._synthesis_worker(
                worker_id=0,
                problem_id="p1",
                node_name="Electromagnetism.Charge",
                prompt_context="",
                dep_chunks=[],
                base_imports=["import Mathlib"],
                stop_event=threading.Event(),
                direct_deps_str="(No direct dependencies)",
            )

            self.assertIsNone(result)
            node_dir = Path(tmpdir) / "Electromagnetism.Charge"
            candidate = node_dir / "attempt_01_candidate.lean"
            compile_input = node_dir / "attempt_01_compile_input.lean"
            error = node_dir / "attempt_01_compile_error.txt"

            self.assertIn("def BadCharge", candidate.read_text(encoding="utf-8"))
            self.assertIn("import Mathlib", compile_input.read_text(encoding="utf-8"))
            self.assertIn("MissingType", error.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
