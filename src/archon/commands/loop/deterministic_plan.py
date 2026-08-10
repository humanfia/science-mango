"""Deterministic objective selection for bounded prover-stage planning.

The planner is useful for proof strategy, but it should not spend tens of
minutes rediscovering which files are eligible for dispatch.  This module
selects that frontier from loop-owned state, writes the exact objective set,
and prepares a bounded evidence pack for the plan agent.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from archon.commands.tooling.blueprint import chapter_coverage_map
from archon.commands.tooling.domain_profile import load_domain_profile
from archon.state.iter_state import objectives_sidecar_path

from .formalization_review_gate import load_gate_state
from .proof_review_gate import load_proof_review_state
from .shared_infrastructure import pending_shared_infrastructure_objectives


_SORRY_RE = re.compile(
    r"(?<![A-Za-z0-9_!?'])(?:sorry|sorryAx|admit)(?![A-Za-z0-9_!?'])"
)
_SKIP_DIRS = {".archon", ".git", ".lake", "lake-packages", "_target"}


@dataclass(frozen=True)
class DeterministicCandidate:
    path: Path
    relative_path: str
    sorry_count: int
    proof_status: str
    proof_attempts: int
    proof_reason: str
    chapter: Path | None
    physics: bool
    prover_mode: str | None = None
    objective_task: str | None = None


def _strip_lean_line(line: str, block_depth: int) -> tuple[str, int]:
    """Return code-only text and updated nested-comment depth."""
    result: list[str] = []
    i = 0
    in_string = False
    while i < len(line):
        ch = line[i]
        nxt = line[i + 1] if i + 1 < len(line) else ""
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < len(line):
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == "-" and nxt == "-":
            break
        if ch == "/" and nxt == "-":
            block_depth += 1
            i += 2
            continue
        result.append(ch)
        i += 1
    return "".join(result), block_depth


def fast_open_sorry_count(path: Path) -> int | None:
    """Count Lean placeholders without spawning one analyzer per file."""
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError:
        return None
    total = 0
    block_depth = 0
    for line in lines:
        code, block_depth = _strip_lean_line(line, block_depth)
        total += len(_SORRY_RE.findall(code))
    return total


def _all_project_lean_files(project_path: Path) -> list[Path]:
    return sorted(
        path.resolve()
        for path in project_path.rglob("*.lean")
        if not any(part in _SKIP_DIRS for part in path.relative_to(project_path).parts)
    )


def _relative(path: Path, project_path: Path) -> str:
    return path.resolve().relative_to(project_path.resolve()).as_posix()


def _chapter_lookup(project_path: Path) -> dict[str, Path]:
    """Build Lean-to-chapter ownership once per selection pass."""
    chapters_dir = project_path / "blueprint" / "src" / "chapters"
    lookup: dict[str, Path] = {}
    for slug, covers in chapter_coverage_map(project_path).items():
        chapter = chapters_dir / f"{slug}.tex"
        if chapter.is_file():
            for rel in covers:
                lookup.setdefault(str(rel).replace("\\", "/"), chapter)
    return lookup


def select_deterministic_candidates(
    *,
    project_path: Path,
    state_dir: Path,
    stage: str,
    limit: int,
    formalization_gate_enabled: bool,
    proof_gate_enabled: bool,
) -> list[DeterministicCandidate]:
    """Select a stable, Review-safe prover frontier with retries first."""
    canonical = stage.strip().lower()
    if not canonical.startswith(("prover", "polish")) or limit <= 0:
        return []
    domain_profile = load_domain_profile(project_path)

    # Shared project-local infrastructure is a prerequisite frontier, not a
    # theorem corpus target.  It bypasses the per-problem formalization gate
    # and retains its explicit mathlib-build mode through deterministic Plan's
    # post-agent objective restore.
    candidates: list[DeterministicCandidate] = []
    shared_paths: set[str] = set()
    for shared in pending_shared_infrastructure_objectives(
        state_dir=state_dir, project_path=project_path,
    ):
        path = (project_path / shared.module_path).resolve()
        if not path.is_file():
            # A missing module needs the full planner + configured structural
            # subagent; PlanPhase disables bounded mode for that case.
            continue
        sorry_count = fast_open_sorry_count(path)
        if sorry_count is None:
            continue
        shared_paths.add(shared.module_path)
        declarations = ", ".join(shared.declarations) or "requested declarations"
        dependents = ", ".join(shared.dependents) or "dependent targets"
        candidates.append(DeterministicCandidate(
            path=path,
            relative_path=shared.module_path,
            sorry_count=sorry_count,
            proof_status="shared_infrastructure",
            proof_attempts=0,
            proof_reason=shared.reason,
            chapter=None,
            physics=False,
            prover_mode=shared.mode,
            objective_task=(
                f"build shared project-local infrastructure axiom-clean "
                f"({declarations}) before retrying {dependents}"
            ),
        ))
        if len(candidates) >= limit:
            return candidates

    # Never mix infrastructure builders with problem provers. The dedicated
    # axiom/build gate owns this batch; dependent problems remain quarantined
    # until consumer imports pass their own full-build check.
    if candidates:
        return candidates

    formal_state = load_gate_state(state_dir) if formalization_gate_enabled else None
    formal_targets = formal_state.get("targets", {}) if formal_state else {}
    if formalization_gate_enabled:
        universe = [
            (project_path / rel).resolve()
            for rel, record in formal_targets.items()
            if isinstance(record, dict) and record.get("status") == "passed"
        ]
    else:
        universe = _all_project_lean_files(project_path)

    proof_state = load_proof_review_state(state_dir) if proof_gate_enabled else {}
    proof_targets = proof_state.get("targets", {}) if isinstance(proof_state, dict) else {}
    if not isinstance(proof_targets, dict):
        proof_targets = {}

    chapters_by_rel = _chapter_lookup(project_path)
    ranked: list[tuple[tuple[int, int, str], Path, str, dict[str, Any]]] = []
    seen: set[str] = set()
    for path in universe:
        try:
            rel = _relative(path, project_path)
        except ValueError:
            continue
        if rel in seen or not path.is_file():
            continue
        if rel in shared_paths:
            continue
        seen.add(rel)
        raw_record = proof_targets.get(rel, {}) if proof_gate_enabled else {}
        record = raw_record if isinstance(raw_record, dict) else {}
        status = str(record.get("status") or "new")
        if status in {
            "solved", "proof_review_exhausted", "needs_redraft",
            "blocked_infrastructure",
        }:
            continue
        attempts = int(record.get("attempts") or 0)
        retry_rank = 0 if status == "retry" else 1
        ranked.append(((retry_rank, -attempts, rel), path, rel, record))

    for _rank, path, rel, record in sorted(ranked, key=lambda item: item[0]):
        sorry_count = fast_open_sorry_count(path)
        status = str(record.get("status") or "new")
        # A Review retry may have no remaining `sorry`: the prior prover can
        # replace the placeholder with a term that fails direct elaboration.
        # Those targets still need a repair lane and must remain ahead of new
        # open-sorry work.
        if sorry_count is None or (sorry_count == 0 and status != "retry"):
            continue
        chapter = chapters_by_rel.get(rel)
        physics = False
        if chapter is not None:
            try:
                chapter_text = chapter.read_text(
                    encoding="utf-8", errors="ignore",
                )
                physics = any(
                    marker in chapter_text
                    for marker in domain_profile.blueprint_markers
                )
            except OSError:
                pass
        candidates.append(
            DeterministicCandidate(
                path=path,
                relative_path=rel,
                sorry_count=sorry_count,
                proof_status=status,
                proof_attempts=int(record.get("attempts") or 0),
                proof_reason=str(record.get("reason") or ""),
                chapter=chapter,
                physics=physics,
                prover_mode=(
                    domain_profile.mode_for_stage("prover")
                    if physics else None
                ),
            )
        )
        if len(candidates) >= limit:
            break
    return candidates


def _replace_objectives(progress_file: Path, lines: Iterable[str]) -> None:
    text = progress_file.read_text(encoding="utf-8")
    body = "## Current Objectives\n\n" + "\n".join(lines).rstrip() + "\n\n"
    pattern = re.compile(
        r"^## Current Objectives\s*\n.*?(?=^## |\Z)",
        flags=re.MULTILINE | re.DOTALL,
    )
    if pattern.search(text):
        text = pattern.sub(body, text, count=1)
    else:
        text = text.rstrip() + "\n\n" + body
    progress_file.write_text(text, encoding="utf-8")


def deterministic_objective_lines(
    candidates: Iterable[DeterministicCandidate],
) -> list[str]:
    lines: list[str] = []
    for index, candidate in enumerate(candidates, start=1):
        if candidate.objective_task:
            task = candidate.objective_task
        elif candidate.proof_status == "retry":
            task = (
                f"mandatory proof-Review retry {candidate.proof_attempts}; "
                "repair the reviewed Lean elaboration/faithfulness failure"
            )
        else:
            task = (
                f"new proof target; fill {candidate.sorry_count} open Lean "
                "placeholder(s)"
            )
        mode_name = candidate.prover_mode or (
            "physics" if candidate.physics else None
        )
        mode = f" [prover-mode: {mode_name}]" if mode_name else ""
        lines.append(
            f"{index}. **`{candidate.relative_path}`** — Deterministically "
            f"selected {task} without weakening the statement.{mode}"
        )
    return lines


def write_deterministic_objectives(
    *,
    progress_file: Path,
    state_dir: Path,
    iter_num: int,
    candidates: list[DeterministicCandidate],
) -> None:
    lines = deterministic_objective_lines(candidates)
    _replace_objectives(progress_file, lines)
    sidecar = objectives_sidecar_path(state_dir, iter_num)
    sidecar.parent.mkdir(parents=True, exist_ok=True)
    sidecar.write_text(
        "# Deterministic Objectives\n\n"
        + "\n".join(lines).rstrip()
        + "\n",
        encoding="utf-8",
    )


def _excerpt(path: Path | None, *, max_chars: int) -> str:
    if path is None:
        return "(missing)"
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return "(unreadable)"
    if len(text) <= max_chars:
        return text.strip()
    sorry_at = min(
        (match.start() for match in _SORRY_RE.finditer(text)),
        default=max(0, len(text) - max_chars // 2),
    )
    start = max(0, sorry_at - max_chars // 2)
    end = min(len(text), start + max_chars)
    return (
        ("... [prefix omitted]\n" if start else "")
        + text[start:end].strip()
        + ("\n... [suffix omitted]" if end < len(text) else "")
    )


def write_deterministic_candidate_pack(
    *,
    project_path: Path,
    iter_dir: Path,
    iter_num: int,
    candidates: list[DeterministicCandidate],
) -> Path:
    """Write the only corpus evidence the bounded planner should inspect."""
    path = iter_dir / "deterministic-plan-candidates.md"
    lines = [
        "# Deterministic Plan Candidate Pack",
        "",
        f"Iteration: {iter_num:03d}",
        f"Exact objective count: {len(candidates)}",
        "",
        "The loop has already selected and written these objectives. Do not scan",
        "the rest of the corpus and do not replace, reorder, add, or remove targets.",
        "Use the excerpts below only to write a concise per-target proof strategy.",
        "",
    ]
    for index, candidate in enumerate(candidates, start=1):
        chapter_rel = (
            candidate.chapter.relative_to(project_path).as_posix()
            if candidate.chapter is not None else "(missing)"
        )
        lines.extend([
            f"## {index}. `{candidate.relative_path}`",
            "",
            f"- Open placeholders: {candidate.sorry_count}",
            f"- Proof Review: {candidate.proof_status}; attempts={candidate.proof_attempts}",
            f"- Review reason: {candidate.proof_reason or '(none)' }",
            f"- Blueprint: `{chapter_rel}`",
            "",
            "### Lean excerpt",
            "```lean",
            _excerpt(candidate.path, max_chars=3000),
            "```",
            "",
            "### Blueprint excerpt",
            "```tex",
            _excerpt(candidate.chapter, max_chars=2500),
            "```",
            "",
        ])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return path


def deterministic_plan_prompt_prefix(
    *,
    candidate_pack: Path,
    plan_input_pack: Path,
    state_dir: Path,
    iter_num: int,
    project_name: str = "",
    project_path: Path | None = None,
    stage: str = "prover",
    captured_user_hints: str | None = None,
    captured_auto_notes: str | None = None,
) -> str:
    """Build the complete short prompt; never invoke the full frontier builder."""
    plan_sidecar = state_dir / "iter" / f"iter-{iter_num:03d}" / "plan.md"

    def clean(value: str | None) -> str:
        text = re.sub(r"<!--.*?-->", "", value or "", flags=re.DOTALL).strip()
        return text[:8000].rstrip() + ("\n... [truncated]" if len(text) > 8000 else "")

    hints = clean(captured_user_hints)
    notes = clean(captured_auto_notes)
    blocks = [
        "DETERMINISTIC BOUNDED PLAN MODE IS ACTIVE.",
        f"Project: {project_name or (project_path.name if project_path else 'project')}",
        f"Project directory: {project_path or '(see input pack)'}",
        f"Stage: {stage}; iteration: {iter_num:03d}.",
        f"Read `{plan_input_pack}` and `{candidate_pack}`.",
        "The loop already selected and wrote the exact Current Objectives. "
        "Do not replace, reorder, add, or remove them.",
        "Do not run repository-wide find/rg/grep, do not enumerate the corpus, "
        "do not invoke leandag/frontier scans, and do not rebuild "
        "task_pending/task_done.",
        "Make one bounded pass over the supplied excerpts. Write a concise, "
        f"actionable per-target proof strategy to `{plan_sidecar}`.",
        "You may edit only the listed blueprint chapters when an excerpt has "
        "a concrete strategy defect; do not edit Lean source files in Plan.",
        "Preserve every source hypothesis, side condition, and requested conclusion; "
        "do not weaken theorem statements.",
        "Finish immediately after the bounded plan sidecar and any necessary "
        "listed-chapter corrections are written.",
    ]
    if hints:
        blocks.extend(["", "## User hints", hints])
    if notes:
        blocks.extend(["", "## Automated validation notes", notes])
    return "\n".join(blocks).rstrip() + "\n\n"
