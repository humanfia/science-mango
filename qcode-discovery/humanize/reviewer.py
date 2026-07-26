"""Independent, read-only Codex review for qcode search rounds."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any


REVIEW_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "type": "object",
    "additionalProperties": False,
    "required": ["verdict", "summary", "risks", "recommended_focus", "lessons"],
    "properties": {
        "verdict": {
            "type": "string",
            "enum": ["continue", "promote", "stop", "reject_round"],
        },
        "summary": {"type": "string", "minLength": 1},
        "risks": {
            "type": "array",
            "items": {
                "type": "object",
                "additionalProperties": False,
                "required": ["severity", "finding", "evidence"],
                "properties": {
                    "severity": {
                        "type": "string", "enum": ["P0", "P1", "P2", "P3"]
                    },
                    "finding": {"type": "string", "minLength": 1},
                    "evidence": {"type": "string", "minLength": 1},
                },
            },
        },
        "recommended_focus": {
            "type": "array", "items": {"type": "string", "minLength": 1}
        },
        "lessons": {
            "type": "array",
            "items": {
                "type": "object",
                "additionalProperties": False,
                "required": ["insight", "evidence", "action"],
                "properties": {
                    "insight": {"type": "string", "minLength": 1},
                    "evidence": {"type": "string", "minLength": 1},
                    "action": {"type": "string", "minLength": 1},
                },
            },
        },
    },
}


class ReviewError(RuntimeError):
    """The independent review failed or violated its output contract."""


def validate_review(value: Any) -> dict[str, Any]:
    """Small runtime validator; Codex also receives the full JSON schema."""
    if not isinstance(value, dict):
        raise ReviewError("review output must be a JSON object")
    required = {"verdict", "summary", "risks", "recommended_focus", "lessons"}
    missing = required - value.keys()
    if missing:
        raise ReviewError("review output missing fields: " + ", ".join(sorted(missing)))
    if value["verdict"] not in {"continue", "promote", "stop", "reject_round"}:
        raise ReviewError(f"invalid review verdict: {value['verdict']!r}")
    if not isinstance(value["summary"], str) or not value["summary"].strip():
        raise ReviewError("review summary must be non-empty")
    if not all(isinstance(value[name], list)
               for name in ("risks", "recommended_focus", "lessons")):
        raise ReviewError("review risks, recommended_focus, and lessons must be arrays")
    for risk in value["risks"]:
        if not isinstance(risk, dict) or risk.get("severity") not in {
            "P0", "P1", "P2", "P3"
        }:
            raise ReviewError("every risk needs severity P0-P3")
        if not str(risk.get("finding", "")).strip() or not str(
            risk.get("evidence", "")
        ).strip():
            raise ReviewError("every risk needs a finding and evidence")
    for lesson in value["lessons"]:
        if not isinstance(lesson, dict) or any(
            not str(lesson.get(field, "")).strip()
            for field in ("insight", "evidence", "action")
        ):
            raise ReviewError("every lesson needs insight, evidence, and action")
    return value


def build_review_prompt(
    *,
    round_number: int,
    contract: dict[str, Any],
    candidates: list[dict[str, Any]],
    audited: list[dict[str, Any]],
    archive_top: list[dict[str, Any]],
    memory: str,
) -> str:
    """Build an evidence-only review prompt with explicit trust boundaries."""
    evidence = {
        "round": round_number,
        "contract": contract,
        "new_candidate_count": len(candidates),
        "new_candidates": candidates[:20],
        "milp_audited": audited,
        "archive_top": archive_top[:20],
    }
    return f"""You are the independent reviewer in a Humanize-style RLCR loop for
quantum error-correcting code discovery. Review the round evidence below. You
did not generate these candidates and must remain skeptical.

Trust boundary:
- Python rank calculations can propose k but do not constitute a Lean proof.
- BP-OSD returns an upper bound on distance, never a lower bound or exact d.
- A MILP result is exact only when every logical direction was solved to proven
  optimality and milp_details.exact is true.
- Your review cannot upgrade any numerical claim. Only MILP certificates and
  later Lean compilation can do so.
- Flag stale or physically implausible FOM claims, duplicated candidates,
  partial MILP coverage, and selection bias.

Verdicts:
- continue: search another round with the recommended focus.
- promote: the audited set is worth sending to Lean now; search may continue.
- stop: enough exact, high-quality evidence exists to end search.
- reject_round: evidence is corrupt or misleading; do not learn from it.

Long-term BitLesson memory (may be empty):
---
{memory[-12000:]}
---

Round evidence JSON:
{json.dumps(evidence, ensure_ascii=False, indent=2, default=str)}

Return only the JSON object required by the supplied output schema. Lessons
must be evidence-backed and reusable; omit speculative lessons.
"""


class CodexReviewer:
    """Invoke a fresh Codex session as the independent round reviewer."""

    def __init__(
        self,
        *,
        repo_dir: Path,
        model: str,
        effort: str,
        timeout: int = 5400,
        codex_bin: str = "codex",
    ):
        self.repo_dir = repo_dir
        self.model = model
        self.effort = effort
        self.timeout = timeout
        self.codex_bin = codex_bin

    def review(self, prompt: str, round_dir: Path) -> dict[str, Any]:
        schema_path = round_dir / "review-schema.json"
        output_path = round_dir / "review.json"
        schema_path.write_text(json.dumps(REVIEW_SCHEMA, indent=2) + "\n")
        command = [
            self.codex_bin,
            "exec",
            "--model", self.model,
            "--config", f'model_reasoning_effort="{self.effort}"',
            "--sandbox", "read-only",
            "--ephemeral",
            "--cd", str(self.repo_dir),
            "--output-schema", str(schema_path),
            "--output-last-message", str(output_path),
            "-",
        ]
        log_path = round_dir / "review.log"
        with log_path.open("w", encoding="utf-8") as log_stream:
            try:
                subprocess.run(
                    command,
                    input=prompt,
                    text=True,
                    stdout=log_stream,
                    stderr=subprocess.STDOUT,
                    timeout=self.timeout,
                    check=True,
                )
            except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
                raise ReviewError(f"independent Codex review failed; see {log_path}") from exc
        if not output_path.is_file():
            raise ReviewError(f"independent Codex review produced no output; see {log_path}")
        try:
            value = json.loads(output_path.read_text())
        except json.JSONDecodeError as exc:
            raise ReviewError(f"independent review was not valid JSON: {output_path}") from exc
        return validate_review(value)
