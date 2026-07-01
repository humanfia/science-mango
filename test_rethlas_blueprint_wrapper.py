from __future__ import annotations

import importlib.util
import io
import json
import subprocess
import sys
import tempfile
import unittest
import urllib.error
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "rethlas_blueprint.py"


def load_wrapper():
    spec = importlib.util.spec_from_file_location("rethlas_blueprint_wrapper", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class RethlasBlueprintWrapperTests(unittest.TestCase):
    def test_wrapper_writes_problem_and_prints_verified_blueprint(self):
        wrapper = load_wrapper()
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "Rethlas"
            generation = root / "agents" / "generation"
            (generation / "tests").mkdir(parents=True)
            (generation / "tests" / "run_example.sh").write_text("#!/usr/bin/env bash\n", encoding="utf-8")

            def fake_run_rethlas(*, generation_root, problem_file, **_kwargs):
                self.assertEqual(problem_file, "data/archon_physics/952.md")
                problem_text = (generation_root / problem_file).read_text(encoding="utf-8")
                self.assertIn("square current loop", problem_text)
                self.assertIn("-I B0 L j", problem_text)
                result = generation_root / "results" / "archon_physics" / "952"
                result.mkdir(parents=True)
                (result / "blueprint_verified.md").write_text(
                    "Verified proof route from Rethlas.\n",
                    encoding="utf-8",
                )
                return subprocess.CompletedProcess(["fake"], 0, stdout="ran\n", stderr="")

            payload = {
                "index": "952",
                "question": "A square current loop is in a magnetic field.",
                "answer": "-I B0 L j",
                "declarations": [{"kind": "theorem", "full_name": "problem_952"}],
            }
            stdout = io.StringIO()
            stderr = io.StringIO()
            argv = [
                "rethlas_blueprint.py",
                "--rethlas-root",
                str(root),
                "--max-iterations",
                "1",
            ]
            with mock.patch.object(wrapper, "run_rethlas", side_effect=fake_run_rethlas), \
                mock.patch.object(sys, "argv", argv), \
                mock.patch("sys.stdin", io.StringIO(json.dumps(payload))), \
                redirect_stdout(stdout), \
                redirect_stderr(stderr):
                self.assertEqual(wrapper.main(), 0)

            self.assertIn("Verified proof route from Rethlas.", stdout.getvalue())
            self.assertIn("ran", stderr.getvalue())

    def test_wrapper_uses_draft_when_unverified_by_default(self):
        wrapper = load_wrapper()
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "Rethlas"
            generation = root / "agents" / "generation"
            (generation / "tests").mkdir(parents=True)
            (generation / "tests" / "run_example.sh").write_text("#!/usr/bin/env bash\n", encoding="utf-8")

            def fake_run_rethlas(*, generation_root, problem_file, **_kwargs):
                result = generation_root / "results" / "archon_physics" / "p1"
                result.mkdir(parents=True)
                (result / "blueprint.md").write_text("Draft route.\n", encoding="utf-8")
                return subprocess.CompletedProcess(["fake"], 1, stdout="", stderr="not verified\n")

            stdout = io.StringIO()
            stderr = io.StringIO()
            argv = ["rethlas_blueprint.py", "--rethlas-root", str(root)]
            with mock.patch.object(wrapper, "run_rethlas", side_effect=fake_run_rethlas), \
                mock.patch.object(sys, "argv", argv), \
                mock.patch("sys.stdin", io.StringIO(json.dumps({"index": "p1", "question": "Q"}))), \
                redirect_stdout(stdout), \
                redirect_stderr(stderr):
                self.assertEqual(wrapper.main(), 0)

            self.assertIn("Draft route.", stdout.getvalue())
            self.assertIn("using draft blueprint.md", stderr.getvalue())

    def test_direct_chat_posts_problem_and_prints_blueprint(self):
        wrapper = load_wrapper()
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "Rethlas"
            generation = root / "agents" / "generation"
            generation.mkdir(parents=True)

            requests = []

            class FakeResponse:
                def __enter__(self):
                    return self

                def __exit__(self, *_args):
                    return None

                def read(self):
                    return json.dumps(
                        {
                            "choices": [
                                {
                                    "message": {
                                        "content": "Direct Claude proof route."
                                    }
                                }
                            ]
                        }
                    ).encode("utf-8")

            def fake_urlopen(request, timeout):
                requests.append((request, timeout))
                return FakeResponse()

            payload = {
                "index": "p2",
                "question": "A particle moves under constant acceleration.",
                "answer": "v = v0 + a t",
            }
            stdout = io.StringIO()
            stderr = io.StringIO()
            argv = [
                "rethlas_blueprint.py",
                "--rethlas-root",
                str(root),
                "--direct-chat",
                "--base-url",
                "http://example.test/v1",
                "--api-key-env",
                "TEST_GATEWAY_KEY",
                "--model",
                "claude-test",
            ]
            with mock.patch.object(sys, "argv", argv), \
                mock.patch.dict("os.environ", {"TEST_GATEWAY_KEY": "secret"}, clear=False), \
                mock.patch("sys.stdin", io.StringIO(json.dumps(payload))), \
                mock.patch("urllib.request.urlopen", side_effect=fake_urlopen), \
                redirect_stdout(stdout), \
                redirect_stderr(stderr):
                self.assertEqual(wrapper.main(), 0)

            self.assertEqual(len(requests), 1)
            request, timeout = requests[0]
            self.assertEqual(request.full_url, "http://example.test/v1/chat/completions")
            self.assertEqual(timeout, 120)
            body = json.loads(request.data.decode("utf-8"))
            self.assertEqual(body["model"], "claude-test")
            self.assertIn("constant acceleration", body["messages"][-1]["content"])
            self.assertIn("Direct Claude proof route.", stdout.getvalue())
            result = generation / "results" / "archon_physics" / "p2" / "blueprint.md"
            self.assertEqual(result.read_text(encoding="utf-8"), "Direct Claude proof route.\n")

    def test_direct_chat_reports_http_error_body(self):
        wrapper = load_wrapper()
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "Rethlas"
            (root / "agents" / "generation").mkdir(parents=True)
            error = urllib.error.HTTPError(
                "http://example.test/v1/chat/completions",
                500,
                "bad",
                hdrs=None,
                fp=io.BytesIO(b'{"error":{"message":"not implemented"}}'),
            )
            argv = [
                "rethlas_blueprint.py",
                "--rethlas-root",
                str(root),
                "--direct-chat",
                "--base-url",
                "http://example.test/v1",
                "--api-key-env",
                "TEST_GATEWAY_KEY",
            ]
            stderr = io.StringIO()
            with mock.patch.object(sys, "argv", argv), \
                mock.patch.dict("os.environ", {"TEST_GATEWAY_KEY": "secret"}, clear=False), \
                mock.patch("sys.stdin", io.StringIO(json.dumps({"index": "p3", "question": "Q"}))), \
                mock.patch("urllib.request.urlopen", side_effect=error), \
                redirect_stderr(stderr):
                self.assertEqual(wrapper.main(), 1)

            self.assertIn("not implemented", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
