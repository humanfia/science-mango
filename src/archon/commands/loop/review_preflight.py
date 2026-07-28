"""Bounded, parallel evidence preparation for deterministic Review."""

from __future__ import annotations

import json
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from pathlib import Path

from .deterministic_plan import fast_open_sorry_count


@dataclass(frozen=True)
class ReviewPreflightCheck:
    file: str
    status: str
    compiles: bool
    returncode: int | None
    sorry_count: int | None
    duration_secs: float
    diagnostics: str


def _relative(path: Path, project_path: Path) -> str:
    try:
        return path.resolve().relative_to(project_path.resolve()).as_posix()
    except ValueError:
        return str(path)


def _check_target(
    project_path: Path,
    target: Path,
    *,
    timeout_sec: int,
) -> ReviewPreflightCheck:
    rel = _relative(target, project_path)
    sorry_count = fast_open_sorry_count(target)
    if not target.is_file():
        return ReviewPreflightCheck(
            rel, "missing", False, None, sorry_count, 0.0, "target file is missing"
        )
    start = time.monotonic()
    try:
        result = subprocess.run(
            ["lake", "env", "lean", rel],
            cwd=project_path,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
        duration = time.monotonic() - start
        diagnostics = ((result.stdout or "") + (result.stderr or "")).strip()
        if len(diagnostics) > 4000:
            diagnostics = diagnostics[:4000].rstrip() + "\n... [truncated]"
        return ReviewPreflightCheck(
            rel,
            "passed" if result.returncode == 0 else "failed",
            result.returncode == 0,
            result.returncode,
            sorry_count,
            round(duration, 3),
            diagnostics,
        )
    except subprocess.TimeoutExpired as exc:
        duration = time.monotonic() - start
        diagnostics = str(exc.stderr or exc.stdout or "direct Lean check timed out")
        return ReviewPreflightCheck(
            rel, "timeout", False, None, sorry_count, round(duration, 3),
            diagnostics[:4000],
        )
    except OSError as exc:
        duration = time.monotonic() - start
        return ReviewPreflightCheck(
            rel, "error", False, None, sorry_count, round(duration, 3), str(exc),
        )


def check_review_target(
    *,
    project_path: Path,
    target: Path,
    timeout_sec: int = 300,
) -> dict:
    """Run the deterministic Review preflight for one completed target."""
    return asdict(
        _check_target(project_path, target.resolve(), timeout_sec=timeout_sec)
    )


def run_parallel_review_preflight(
    *,
    project_path: Path,
    objectives: list[Path],
    iter_dir: Path,
    iter_num: int,
    jobs: int,
    timeout_sec: int = 300,
) -> dict:
    """Run direct Lean checks concurrently and write stable JSON/Markdown."""
    ordered = list(dict.fromkeys(path.resolve() for path in objectives))
    workers = max(1, min(jobs, len(ordered))) if ordered else 1
    start = time.monotonic()
    by_path: dict[Path, ReviewPreflightCheck] = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        pending = {
            pool.submit(
                _check_target, project_path, path, timeout_sec=timeout_sec
            ): path
            for path in ordered
        }
        for future in as_completed(pending):
            path = pending[future]
            try:
                by_path[path] = future.result()
            except Exception as exc:
                by_path[path] = ReviewPreflightCheck(
                    _relative(path, project_path),
                    "error",
                    False,
                    None,
                    fast_open_sorry_count(path),
                    0.0,
                    str(exc),
                )
    checks = [by_path[path] for path in ordered]
    duration = round(time.monotonic() - start, 3)
    summary = {
        "total": len(checks),
        "passed": sum(check.compiles for check in checks),
        "failed": sum(not check.compiles for check in checks),
    }
    payload = {
        "iteration": iter_num,
        "jobs": workers,
        "duration_secs": duration,
        "summary": summary,
        "targets": [asdict(check) for check in checks],
    }
    iter_dir.mkdir(parents=True, exist_ok=True)
    json_path = iter_dir / "review-preflight.json"
    md_path = iter_dir / "review-preflight.md"
    json_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    lines = [
        "# Parallel Lean Review Preflight",
        "",
        f"- Iteration: {iter_num:03d}",
        f"- Jobs: {workers}",
        f"- Duration: {duration:.3f}s",
        f"- Result: {summary['passed']} passed / {summary['failed']} failed",
        "",
        "| Target | Compile | Sorries | Seconds |",
        "| --- | ---: | ---: | ---: |",
    ]
    for check in checks:
        lines.append(
            f"| `{check.file}` | {check.status} | "
            f"{check.sorry_count if check.sorry_count is not None else '?'} | "
            f"{check.duration_secs:.3f} |"
        )
        if check.diagnostics:
            lines.extend([
                "",
                f"## `{check.file}` diagnostics",
                "```text",
                check.diagnostics,
                "```",
            ])
    md_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return {**payload, "json_path": json_path, "md_path": md_path}


def _excerpt(path: Path | None, max_chars: int) -> str:
    if path is None:
        return "(missing)"
    try:
        text = path.read_text(encoding="utf-8", errors="ignore").strip()
    except OSError:
        return "(unreadable)"
    if len(text) <= max_chars:
        return text
    return text[-max_chars:].lstrip() + "\n... [leading content omitted]"


def write_deterministic_review_pack(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    objectives: list[Path],
    preflight: dict,
) -> Path:
    """Write bounded semantic evidence for only the current objectives."""
    checks = {
        row["file"]: row for row in preflight.get("targets", [])
        if isinstance(row, dict) and row.get("file")
    }
    task_dir = state_dir / "task_results"
    lines = [
        "# Deterministic Review Candidate Pack",
        "",
        f"Iteration: {iter_num:03d}",
        f"Exact review target count: {len(objectives)}",
        "",
        "Review only these targets. Direct Lean compilation was already run in",
        "parallel by the orchestrator; use the recorded result instead of rerunning it.",
        "",
    ]
    for index, target in enumerate(objectives, start=1):
        rel = _relative(target, project_path)
        slug = rel.removesuffix(".lean").replace("/", "_")
        chapter = (
            project_path / "blueprint" / "src" / "chapters" / f"{slug}.tex"
        )
        reports = sorted(
            task_dir.glob(f"*{target.stem}*.md"),
            key=lambda path: path.stat().st_mtime,
            reverse=True,
        )[:2] if task_dir.is_dir() else []
        check = checks.get(rel, {})
        lines.extend([
            f"## {index}. `{rel}`",
            "",
            f"- Compile status: {check.get('status', 'unknown')}",
            f"- Open sorries: {check.get('sorry_count', 'unknown')}",
            f"- Direct-check seconds: {check.get('duration_secs', 'unknown')}",
            f"- Blueprint: `{_relative(chapter, project_path)}`",
            "- Reports: " + (
                ", ".join(f"`{_relative(path, project_path)}`" for path in reports)
                if reports else "(none)"
            ),
            "",
            "### Lean excerpt",
            "```lean",
            _excerpt(target, 2600),
            "```",
            "",
            "### Blueprint excerpt",
            "```tex",
            _excerpt(chapter, 1800),
            "```",
            "",
        ])
        for report in reports:
            lines.extend([
                f"### Report excerpt: `{report.name}`",
                "```markdown",
                _excerpt(report, 1200),
                "```",
                "",
            ])
    path = iter_dir / "deterministic-review-candidates.md"
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return path


def deterministic_review_prompt_prefix(
    *,
    preflight_path: Path,
    candidate_pack: Path,
    doctor_path: Path,
) -> str:
    return (
        "DETERMINISTIC BOUNDED REVIEW MODE IS ACTIVE.\n"
        f"Read `{preflight_path}` and `{candidate_pack}` first.\n"
        "Review exactly the listed current objectives; do not enumerate or audit "
        "targets outside that set.\n"
        "The orchestrator already ran every direct Lean check in parallel. Do not "
        "run `lake env lean`, `lake build`, or another compile check for a listed "
        "target unless its preflight status is `timeout` or `error`.\n"
        f"Treat `{doctor_path}` as the structural graph/physics-doctor result. "
        "Do not run leandag, rebuild the DAG, or perform repository-wide "
        "find/rg/grep scans.\n"
        "Perform the semantic/faithfulness audit from the bounded excerpts and "
        "target reports, then write all required Review artifacts immediately.\n\n"
    )
