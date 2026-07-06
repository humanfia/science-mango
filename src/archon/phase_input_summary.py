"""Compact phase input packs for plan/review ablations.

These packs are deterministic summaries of the files phase agents commonly
read first. They are not meant to replace the source files permanently; they
let an ablation test whether shorter first-pass inputs reduce plan/review
runtime and token growth.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from archon.state.cost import safe_jsonl_lines


_MAX_FILE_CHARS = 3500
_MAX_REPORT_CHARS = 900
_MAX_REPORTS = 8
_MAX_SESSION_SUMMARIES = 8


def _read(path: Path, *, max_chars: int = _MAX_FILE_CHARS) -> str:
    try:
        text = path.read_text(encoding="utf-8", errors="ignore").strip()
    except OSError:
        return ""
    if len(text) <= max_chars:
        return text
    return text[:max_chars].rstrip() + "\n\n... [truncated by compact input pack]"


def _section(text: str, heading: str, *, max_chars: int = 1200) -> str:
    pattern = re.compile(
        rf"(?ms)^##\s+{re.escape(heading)}\s*$" r"(.*?)(?=^##\s+|\Z)"
    )
    match = pattern.search(text)
    if not match:
        return ""
    body = match.group(1).strip()
    if len(body) <= max_chars:
        return body
    return body[:max_chars].rstrip() + "\n... [truncated]"


def _summarize_markdown(path: Path) -> str:
    text = _read(path, max_chars=20000)
    if not text:
        return ""
    pieces: list[str] = []
    for heading in (
        "Summary",
        "Proofs closed",
        "Remaining sorries",
        "Redraft needed",
        "Validation",
        "Grounding Gaps",
        "LeanExplore Queries And Candidates Used",
    ):
        part = _section(text, heading)
        if part:
            pieces.append(f"### {heading}\n{part}")
    if not pieces:
        pieces.append(text[:_MAX_REPORT_CHARS].rstrip())
    out = "\n\n".join(pieces)
    if len(out) > _MAX_REPORT_CHARS:
        out = out[:_MAX_REPORT_CHARS].rstrip() + "\n... [truncated]"
    return out


def _task_result_summaries(state_dir: Path) -> str:
    task_dir = state_dir / "task_results"
    if not task_dir.is_dir():
        return "(no task_results directory)"
    paths = sorted(
        (p for p in task_dir.rglob("*.md") if p.is_file()),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    if not paths:
        return "(no task result reports)"
    chunks: list[str] = []
    for path in paths[:_MAX_REPORTS]:
        rel = path.relative_to(state_dir).as_posix()
        summary = _summarize_markdown(path)
        if summary:
            chunks.append(f"## {rel}\n\n{summary}")
    if len(paths) > _MAX_REPORTS:
        chunks.append(f"... and {len(paths) - _MAX_REPORTS} more report(s) not included")
    return "\n\n".join(chunks) if chunks else "(task result reports were empty)"


def _latest_iter_sidecars(state_dir: Path, current_iter: int, *, window: int = 3) -> str:
    iter_root = state_dir / "iter"
    if not iter_root.is_dir():
        return "(no iter sidecars)"
    nums: list[int] = []
    for path in iter_root.glob("iter-*"):
        if path.is_dir() and path.name[5:].isdigit():
            n = int(path.name[5:])
            if n < current_iter:
                nums.append(n)
    chunks: list[str] = []
    for n in sorted(nums)[-window:]:
        for name in ("plan.md", "review.md", "objectives.md"):
            p = iter_root / f"iter-{n:03d}" / name
            text = _read(p, max_chars=1500)
            if text:
                chunks.append(f"## iter-{n:03d}/{name}\n\n{text}")
    return "\n\n".join(chunks) if chunks else "(no recent sidecar content)"


def _session_end_summaries(jsonl_path: Path) -> str:
    rows: list[str] = []
    for line in safe_jsonl_lines(jsonl_path):
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if row.get("event") != "session_end":
            continue
        summary = str(row.get("summary") or "").strip()
        if not summary:
            continue
        summary = summary[:700].rstrip()
        input_total = row.get("input_tokens_total") or row.get("input_tokens") or 0
        output = row.get("output_tokens") or 0
        rows.append(
            f"- tokens in_total={input_total} out={output}\n"
            f"  summary: {summary}"
        )
        if len(rows) >= _MAX_SESSION_SUMMARIES:
            break
    return "\n".join(rows) if rows else "(no session_end summaries found)"


def _doctor_summary(iter_dir: Path) -> str:
    data_path = iter_dir / "blueprint-doctor.json"
    try:
        data = json.loads(data_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        md = _read(iter_dir / "blueprint-doctor.md", max_chars=2500)
        return md or "(no blueprint-doctor report)"
    if not isinstance(data, dict):
        return "(blueprint-doctor JSON was not an object)"
    keys = (
        "orphan_chapters",
        "broken_refs",
        "malformed_refs",
        "axiom_decls",
        "physics_modeling_problems",
        "physics_grounding_problems",
    )
    lines: list[str] = []
    for key in keys:
        items = data.get(key) or []
        if not isinstance(items, list) or not items:
            continue
        lines.append(f"## {key} ({len(items)})")
        for item in items[:8]:
            lines.append(f"- {json.dumps(item, ensure_ascii=False)[:500]}")
        if len(items) > 8:
            lines.append(f"- ... and {len(items) - 8} more")
    return "\n".join(lines) if lines else "(blueprint-doctor has no listed blockers)"


def build_plan_input_pack(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
) -> Path:
    """Write and return a compact first-pass input pack for the plan phase."""

    path = iter_dir / "plan-input-pack.md"
    lines = [
        "# Compact Plan Input Pack",
        "",
        "This pack is generated by Archon for prompt-compression ablation.",
        "Use it as the first-pass replacement for broad scans of AGENTS.md, prompts/plan.md, task_results, and recent iter sidecars.",
        "If a rule or exact file detail is missing, read the source file explicitly.",
        "",
        "## Current PROGRESS.md",
        _read(state_dir / "PROGRESS.md"),
        "",
        "## Current STRATEGY.md",
        _read(state_dir / "STRATEGY.md"),
        "",
        "## Current task_pending.md",
        _read(state_dir / "task_pending.md"),
        "",
        "## Current task_done.md",
        _read(state_dir / "task_done.md"),
        "",
        "## ARCHON_MEMORY.md",
        _read(state_dir / "ARCHON_MEMORY.md"),
        "",
        "## Recent Iter Sidecars",
        _latest_iter_sidecars(state_dir, iter_num),
        "",
        "## Task Result Summaries",
        _task_result_summaries(state_dir),
        "",
        "## Minimal Plan Rules",
        "- Update PROGRESS.md with parseable objectives under `## Current Objectives`.",
        "- Keep STRATEGY.md stable; put iteration narrative in the current iter sidecar.",
        "- Dispatch only useful prover objectives; avoid files with no open sorries.",
        "- Respect archon-protected.yaml and project-local prompts if exact rules are needed.",
        "- For physics chapters, keep physical hypotheses and LeanExplore grounding visible.",
    ]
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return path


def build_review_input_pack(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    attempts_file: Path,
    combined_prover_log: Path,
) -> Path:
    """Write and return a compact first-pass input pack for the review phase."""

    path = iter_dir / "review-input-pack.md"
    lines = [
        "# Compact Review Input Pack",
        "",
        "This pack is generated by Archon for prompt-compression ablation.",
        "Use it as the first-pass replacement for broad scans of prover JSONL logs, attempts_raw.jsonl, and task_results.",
        "If exact evidence is needed, read the source files named below.",
        "",
        "## Source Files",
        f"- attempts: `{attempts_file}`",
        f"- combined prover log: `{combined_prover_log}`",
        f"- task_results: `{state_dir / 'task_results'}`",
        "",
        "## Current PROGRESS.md",
        _read(state_dir / "PROGRESS.md"),
        "",
        "## PROJECT_STATUS.md",
        _read(state_dir / "PROJECT_STATUS.md"),
        "",
        "## Blueprint Doctor Summary",
        _doctor_summary(iter_dir),
        "",
        "## Prover Session Summaries",
        _session_end_summaries(combined_prover_log),
        "",
        "## Task Result Summaries",
        _task_result_summaries(state_dir),
        "",
        "## Recent Iter Sidecars",
        _latest_iter_sidecars(state_dir, iter_num),
        "",
        "## Minimal Review Rules",
        "- Write milestones.jsonl, summary.md, recommendations.md, and PROJECT_STATUS.md as instructed.",
        "- Surface compile, sorry, blueprint, grounding, and physics-modeling blockers.",
        "- Do not mark physics work complete if blueprint-doctor physics blockers remain.",
        "- Prefer the compact pack first; read exact logs only when needed to verify a claim.",
    ]
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return path
