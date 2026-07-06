from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from archon.prompt_compression import (
    PromptCompressionConfig,
    compress_prompt,
    write_prompt_compression_report,
)
from archon.phase_input_summary import (
    build_plan_input_pack,
    build_review_input_pack,
)
from archon.prompts import build_plan_prompt, build_review_prompt


class PromptCompressionTest(unittest.TestCase):
    def test_disabled_is_identity(self):
        prompt = "header\n\n## Per-iteration sidecars\n\n" + ("- detail\n" * 200)
        result = compress_prompt(
            prompt,
            role="plan",
            config=PromptCompressionConfig(enabled=False, section_chars=200),
        )
        self.assertEqual(result.prompt, prompt)
        self.assertFalse(result.report.changed)

    def test_compresses_large_dynamic_plan_section(self):
        prompt = (
            "You are the plan agent.\n\n"
            "    ## Per-iteration sidecars\n\n"
            "Opening context\n"
            + "\n".join(
                f"- iter detail {i}: Foo{i}.lean has blocker sorry and LeanExplore grounding note"
                for i in range(120)
            )
            + "\n\n## Available subagents\n\n"
            "This fixed workflow section should stay verbatim.\n"
        )
        result = compress_prompt(
            prompt,
            role="plan",
            config=PromptCompressionConfig(
                enabled=True,
                target_chars=2500,
                section_chars=1200,
            ),
        )
        self.assertTrue(result.report.changed)
        self.assertLess(len(result.prompt), len(prompt))
        self.assertIn("ARCHON PROMPT COMPRESSION", result.prompt)
        self.assertIn("## Available subagents", result.prompt)
        self.assertIn("This fixed workflow section should stay verbatim.", result.prompt)
        self.assertEqual(result.report.sections[0].title, "Per-iteration sidecars")

    def test_blueprint_graph_is_not_hidden_by_blueprint_exact_protection(self):
        prompt = (
            "header\n\n"
            "## Blueprint graph state (leandag)\n\n"
            + "\n".join(
                f"- ready node {i}: Foo{i}.lean blocker with sorry"
                for i in range(80)
            )
            + "\n\n## Blueprint\n\n"
            + "\n".join("fixed blueprint instruction" for _ in range(80))
        )
        result = compress_prompt(
            prompt,
            role="plan",
            config=PromptCompressionConfig(
                enabled=True,
                target_chars=2000,
                section_chars=600,
            ),
        )
        titles = [s.title for s in result.report.sections]
        self.assertIn("Blueprint graph state (leandag)", titles)
        self.assertNotIn("Blueprint", titles)

    def test_does_not_compress_physics_review_rules(self):
        physics_rules = (
            "## Physics review requirements\n\n"
            + "\n".join(
                "- BLOCKER: theorem statements need physical hypotheses and real calculus operators."
                for _ in range(200)
            )
        )
        result = compress_prompt(
            "Review header\n\n" + physics_rules,
            role="review",
            config=PromptCompressionConfig(
                enabled=True,
                target_chars=2000,
                section_chars=500,
            ),
        )
        self.assertFalse(result.report.changed)
        self.assertNotIn("ARCHON PROMPT COMPRESSION", result.prompt)
        self.assertEqual(result.prompt, "Review header\n\n" + physics_rules)

    def test_report_writer_outputs_json(self):
        prompt = "header\n\n## Blueprint doctor report\n\n" + ("- issue in A.lean\n" * 100)
        result = compress_prompt(
            prompt,
            role="review",
            config=PromptCompressionConfig(enabled=True, section_chars=500),
        )
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "prompt-compression-review.json"
            write_prompt_compression_report(path, result.report)
            data = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(data["role"], "review")
        self.assertIn("original_chars", data)
        self.assertIn("sections", data)


class CompactInputPromptTest(unittest.TestCase):
    def test_plan_prompt_points_to_compact_pack_first(self):
        prompt = build_plan_prompt(
            project_name="proj",
            project_path=Path("/tmp/proj"),
            state_dir=Path("/tmp/proj/.archon"),
            stage="prover",
            iter_num=7,
            compact_input_pack=Path("/tmp/proj/.archon/logs/iter-007/plan-input-pack.md"),
        )
        self.assertIn("COMPACT INPUT MODE is enabled", prompt)
        self.assertIn("plan-input-pack.md", prompt)
        self.assertIn("Do NOT scan those full files", prompt)

    def test_review_prompt_points_to_compact_pack_first(self):
        prompt = build_review_prompt(
            project_name="proj",
            project_path=Path("/tmp/proj"),
            state_dir=Path("/tmp/proj/.archon"),
            stage="prover",
            session_num=7,
            session_dir=Path("/tmp/proj/.archon/proof-journal/sessions/session_7"),
            attempts_file=Path("/tmp/proj/.archon/proof-journal/current_session/attempts_raw.jsonl"),
            combined_prover_log=Path("/tmp/proj/.archon/logs/iter-007/provers-combined.jsonl"),
            iter_num=7,
            compact_input_pack=Path("/tmp/proj/.archon/logs/iter-007/review-input-pack.md"),
        )
        self.assertIn("COMPACT INPUT MODE is enabled", prompt)
        self.assertIn("review-input-pack.md", prompt)
        self.assertIn("Do NOT scan those full", prompt)


class CompactInputPackTest(unittest.TestCase):
    def test_build_plan_input_pack_summarizes_recent_state(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-003"
            task_dir = state / "task_results"
            iter_dir.mkdir(parents=True)
            task_dir.mkdir(parents=True)
            (state / "PROGRESS.md").write_text("## Current Objectives\n- `A.lean`\n", encoding="utf-8")
            (state / "STRATEGY.md").write_text("stable strategy", encoding="utf-8")
            (task_dir / "a.md").write_text(
                "## Summary\nclosed one item\n\n## Grounding Gaps\nnone",
                encoding="utf-8",
            )

            pack = build_plan_input_pack(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=3,
            )
            text = pack.read_text(encoding="utf-8")

        self.assertIn("# Compact Plan Input Pack", text)
        self.assertIn("## Current PROGRESS.md", text)
        self.assertIn("task_results/a.md", text)
        self.assertIn("closed one item", text)

    def test_build_review_input_pack_summarizes_session_end(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            state = root / ".archon"
            iter_dir = state / "logs" / "iter-004"
            iter_dir.mkdir(parents=True)
            (state / "PROGRESS.md").write_text("prover", encoding="utf-8")
            combined = iter_dir / "provers-combined.jsonl"
            combined.write_text(
                json.dumps({
                    "event": "session_end",
                    "summary": "proved helper and left theorem blocked",
                    "input_tokens_total": 1234,
                    "output_tokens": 56,
                }) + "\n",
                encoding="utf-8",
            )
            attempts = state / "proof-journal" / "current_session" / "attempts_raw.jsonl"
            attempts.parent.mkdir(parents=True)
            attempts.write_text("", encoding="utf-8")

            pack = build_review_input_pack(
                project_path=root,
                state_dir=state,
                iter_dir=iter_dir,
                iter_num=4,
                attempts_file=attempts,
                combined_prover_log=combined,
            )
            text = pack.read_text(encoding="utf-8")

        self.assertIn("# Compact Review Input Pack", text)
        self.assertIn("proved helper", text)
        self.assertIn("in_total=1234", text)


if __name__ == "__main__":
    unittest.main()
