"""Independent, read-only Codex review for qcode search rounds."""

from __future__ import annotations

import copy
import json
import subprocess
import time
from collections.abc import Callable
from pathlib import Path
from typing import Any

from .state import candidate_terminal_negative


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


_ADVISORY_ROW_FIELDS = (
    "candidate_key",
    "ell",
    "m",
    "n",
    "k",
    "A_terms",
    "B_terms",
    "archive_cell",
    "archive_round",
    "pattern_type",
    "pattern_classifier_version",
    "term_count",
    "stage",
    "search_status",
    "distance_status",
    "d_is_exact",
    "distance_trusted",
    "milp_attempted",
    "candidate_persistence_lane",
    "candidate_persistence_reason",
    "winner_capable_parameters",
    "minimum_winning_distance",
    "singleton_distance_upper_bound",
    "static_eligibility",
    "structural_novelty",
    "distance_retry_required",
    "distance_backend_error",
)


def _upper_bound_neutral_advisory(row: dict[str, Any]) -> dict[str, Any]:
    """Project an untrusted row without exposing upper-bound reward signals."""
    projected = {
        name: copy.deepcopy(row[name])
        for name in _ADVISORY_ROW_FIELDS
        if name in row
    }
    projected["distance_policy"] = (
        "unresolved upper-bound magnitude withheld; no positive distance "
        "credit"
    )

    details = row.get("milp_details")
    if isinstance(details, dict):
        coverage_fields = (
            "exact",
            "checkpoint_status",
            "total_logicals",
            "num_logicals_checked",
            "logicals_optimal",
            "logicals_incumbent",
            "logicals_timeout",
            "all_timeout",
            "no_incumbent",
        )
        projected["milp_coverage"] = {
            name: copy.deepcopy(details[name])
            for name in coverage_fields
            if name in details
        }

    terminal_negative = candidate_terminal_negative(row)
    if terminal_negative:
        projected["proof_backed_terminal_negative"] = {
            name: copy.deepcopy(row[name])
            for name in (
                "threshold_rejection_proven",
                "threshold_proof_source",
                "threshold_proof_distance",
                "fom_rejection_cutoff",
                "challenge_rejection_cutoff",
                "fom_target_excluded_by_upper_bound",
                "final_gate_excluded_by_upper_bound",
                "search_final_gate_excluded_by_upper_bound",
            )
            if name in row
        }

    if any(
        name in row
        for name in (
            "distance_lower_bound",
            "distance_lower_bound_proven",
            "distance_lower_bound_status",
            "fom_lower_bound",
        )
    ):
        projected["unverified_lower_bound_claim_withheld"] = True
    return projected


def build_review_prompt(
    *,
    round_number: int,
    contract: dict[str, Any],
    candidates: list[dict[str, Any]],
    audited: list[dict[str, Any]],
    archive_top: list[dict[str, Any]],
    memory: str,
    trusted_exact_history: list[dict[str, Any]] | None = None,
    trusted_exact_wins: list[dict[str, Any]] | None = None,
) -> str:
    """Build an evidence-only review prompt with explicit trust boundaries."""
    trusted_exact_history = trusted_exact_history or []
    trusted_exact_wins = trusted_exact_wins or []
    evidence = {
        "round": round_number,
        "contract": contract,
        "new_candidate_count": len(candidates),
        "new_candidates": [
            _upper_bound_neutral_advisory(row)
            for row in candidates[:20]
        ],
        "milp_audited": [
            _upper_bound_neutral_advisory(row)
            for row in audited
        ],
        "archive_top": [
            _upper_bound_neutral_advisory(row)
            for row in archive_top[:20]
        ],
        "upper_bound_neutralization_policy": {
            "bp_osd_distance_and_fom_magnitudes_withheld": True,
            "unreplayed_upper_bounds_cannot_permanently_reject": True,
            "positive_distance_credit_sources": [
                "trusted_exact_history",
            ],
        },
        "trusted_exact_policy": {
            "source": "canonical evaluations.jsonl",
            "classification": "AuditOutcome.EXACT",
            "formal_checkpoint_replay_required": True,
            "challenge_win_rule": "evaluation.final_gate.classify_win",
            "authoritative_construction_rebuild_required": True,
            "explicit_known_code_registry_replay_required": True,
            "registry_novel_true_required_for_stop": True,
        },
        "trusted_exact_history": trusted_exact_history[:20],
        "trusted_exact_wins": trusted_exact_wins[:20],
    }
    return f"""You are the independent reviewer in a Humanize-style RLCR loop for
quantum error-correcting code discovery. Review the round evidence below. You
did not generate these candidates and must remain skeptical.

Trust boundary:
- Python rank calculations can propose k but do not constitute a Lean proof.
- BP-OSD returns an upper bound on distance, never a lower bound or exact d.
- A MILP result is exact only when every logical direction was solved to proven
  optimality and milp_details.exact is true.
- Only trusted_exact_history was independently replayed from the canonical
  audit log. trusted_exact_wins is the subset that also passes a construction
  rebuild and explicit known-code registry replay with novel=true.
- archive_top, new_candidates, and milp_audited are upper-bound-neutral
  projections: unresolved BP/OSD d and FOM magnitudes are deliberately absent.
- A replayable low-weight witness may be used only as negative evidence.
- Positive distance credit requires trusted exact history or a formally
  certified lower bound; survival under BP/OSD is not such a bound.
- Your review cannot upgrade any numerical claim. Only MILP certificates and
  later Lean compilation can do so.
- Flag stale or physically implausible FOM claims, duplicated candidates,
  partial MILP coverage, and selection bias.

Verdicts:
- continue: search another round with the recommended focus.
- promote: the audited set is worth sending to Lean now; search may continue.
- stop: recommend stopping; the controller will honor this only when
  trusted_exact_wins is non-empty.
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
        max_attempts: int = 3,
        retry_backoff_seconds: float = 1.0,
        sleeper: Callable[[float], None] = time.sleep,
    ):
        if max_attempts < 1:
            raise ValueError("max_attempts must be at least 1")
        if retry_backoff_seconds < 0:
            raise ValueError("retry_backoff_seconds must be non-negative")
        self.repo_dir = repo_dir
        self.model = model
        self.effort = effort
        self.timeout = timeout
        self.codex_bin = codex_bin
        self.max_attempts = max_attempts
        self.retry_backoff_seconds = retry_backoff_seconds
        self.sleeper = sleeper

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
        failures: list[ReviewError] = []
        log_paths: list[Path] = []
        for attempt in range(1, self.max_attempts + 1):
            log_path = round_dir / f"review-attempt-{attempt:02d}.log"
            log_paths.append(log_path)
            try:
                with log_path.open("w", encoding="utf-8") as log_stream:
                    log_stream.write(
                        f"[review-attempt] attempt={attempt}/{self.max_attempts} "
                        f"model={self.model} effort={self.effort} "
                        f"timeout_seconds={self.timeout}\n"
                    )
                    log_stream.flush()
                    try:
                        output_path.unlink(missing_ok=True)
                        subprocess.run(
                            command,
                            input=prompt,
                            text=True,
                            stdout=log_stream,
                            stderr=subprocess.STDOUT,
                            timeout=self.timeout,
                            check=True,
                        )
                    except (
                        subprocess.CalledProcessError,
                        subprocess.TimeoutExpired,
                        OSError,
                    ) as exc:
                        raise ReviewError(
                            "independent Codex review process failed "
                            f"on attempt {attempt}/{self.max_attempts}; "
                            f"{type(exc).__name__}: {exc}; "
                            f"see {log_path}"
                        ) from exc

                    if not output_path.is_file():
                        raise ReviewError(
                            "independent Codex review produced no output "
                            f"on attempt {attempt}/{self.max_attempts}; "
                            f"see {log_path}"
                        )
                    try:
                        value = json.loads(output_path.read_text())
                    except (json.JSONDecodeError, OSError) as exc:
                        raise ReviewError(
                            "independent review output was not valid JSON "
                            f"on attempt {attempt}/{self.max_attempts}: "
                            f"{output_path}; see {log_path}"
                        ) from exc
                    try:
                        validated = validate_review(value)
                    except ReviewError as exc:
                        raise ReviewError(
                            "independent review output violated its schema "
                            f"on attempt {attempt}/{self.max_attempts}: {exc}; "
                            f"see {log_path}"
                        ) from exc
                    log_stream.write("\n[review-attempt] status=success\n")
                    return validated
            except ReviewError as exc:
                failures.append(exc)
                try:
                    with log_path.open("a", encoding="utf-8") as log_stream:
                        log_stream.write(f"\n[review-attempt] failure={exc}\n")
                except OSError:
                    pass

            if attempt < self.max_attempts:
                delay = self.retry_backoff_seconds * (2 ** (attempt - 1))
                self.sleeper(delay)

        logs = ", ".join(str(path) for path in log_paths)
        raise ReviewError(
            "independent Codex review failed after "
            f"{self.max_attempts} attempts; see attempt logs: {logs}"
        ) from failures[-1]
