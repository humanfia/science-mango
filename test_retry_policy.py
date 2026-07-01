"""Tests for retry behavior around external model/search calls."""

from __future__ import annotations

import importlib
import sys
import types
import unittest
from pathlib import Path
from unittest import mock


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


class RetryPolicyTests(FormalizerImportMixin, unittest.TestCase):
    def test_llm_api_retries_transient_exceptions_before_returning_response(self):
        config = importlib.import_module("config")
        config.LLM_MAX_RETRIES = 3
        config.LLM_RETRY_DELAY = 1
        config.LLM_MODEL_NAME = "test-model"
        config.SUPPORTS_TEMPERATURE = True
        llm_modules = importlib.import_module("modules.llm_modules")

        class FakeCompletions:
            def __init__(self):
                self.calls = 0

            def create(self, **_kwargs):
                self.calls += 1
                if self.calls < 4:
                    raise RuntimeError("temporary gateway failure")
                return types.SimpleNamespace(
                    choices=[
                        types.SimpleNamespace(
                            message=types.SimpleNamespace(content="  ok  ")
                        )
                    ]
                )

        completions = FakeCompletions()
        module = llm_modules.LLMModules.__new__(llm_modules.LLMModules)
        module.client = types.SimpleNamespace(
            chat=types.SimpleNamespace(completions=completions)
        )

        with mock.patch.object(llm_modules.time, "sleep") as sleep:
            response = module._call_llm_api("prompt")

        self.assertEqual(response, "ok")
        self.assertEqual(completions.calls, 4)
        self.assertEqual(sleep.call_count, 3)

    def test_leanexplore_web_search_retries_transient_exceptions(self):
        config = importlib.import_module("config")
        config.LEANSEARCH_MAX_RETRIES = 3
        config.LEANSEARCH_RETRY_DELAY = 1
        external_tools = importlib.import_module("modules.external_tools")

        client = external_tools.LeanSearchClient.__new__(
            external_tools.LeanSearchClient
        )
        client.num_results = 10
        client.timeout = 30
        client.api_key = "test-key"
        client.search_packages = ["Mathlib"]
        client.use_local = False

        attempts = {"count": 0}

        async def flaky_search(_query):
            attempts["count"] += 1
            if attempts["count"] < 4:
                raise RuntimeError("temporary search failure")
            return [
                types.SimpleNamespace(
                    name="Nat.add_comm",
                    informalization="addition is commutative",
                    source_text="theorem Nat.add_comm",
                )
            ]

        client._search_web_async = flaky_search

        with mock.patch.object(external_tools.time, "sleep") as sleep:
            results = client._search_web("addition commutative")

        self.assertEqual(attempts["count"], 4)
        self.assertEqual(sleep.call_count, 3)
        self.assertEqual(results[0].full_lean_name, "Nat.add_comm")


if __name__ == "__main__":
    unittest.main()
