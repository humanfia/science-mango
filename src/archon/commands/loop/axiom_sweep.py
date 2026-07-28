"""Axiom sweep — catch ``sorryAx`` laundering the sorry count misses.

The headline sorry-count metric is WARNING-based (it parses the literal
``sorry`` token / Lean's sorry warning). That misses a real unsoundness
channel: a declaration that delegates to a ``sorry``-bearing lemma
compiles with NO sorry warning, yet carries ``sorryAx`` in its axiom
set. The loop can then report a stable/decreasing sorry count while the
unsound dependency surface silently grows through clean-compiling
delegates.

This module runs the bundled ``check_axioms_inline.sh`` — which
temporarily appends ``#print axioms`` to a Lean file and recompiles — once per
selected target, concurrently, on private disposable copies. It reports any
top-level declaration that depends on ``sorryAx`` (and, secondarily, any other
non-standard axiom).

Informational only: it never blocks the loop and does not modify source files.
It is comparatively expensive (a per-file recompile), so the phase that calls
it is gated behind ``loop.axiom_sweep`` (off by default).
"""

from __future__ import annotations

import re
import shutil
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Iterable

from archon import log


# The script emits, per offending declaration, a line of the form
#   ``⚠ <decl> uses non-standard axiom: <axiom>``
# wrapped in ANSI colour codes. We strip the colour first, then match.
_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
_FINDING_RE = re.compile(
    r"⚠\s+(?P<decl>[A-Za-z0-9_.]+)\s+uses non-standard axiom:\s+"
    r"(?P<axiom>[A-Za-z0-9_.]+)"
)

# Generous per-target bound. Full polish sweeps can still take many minutes,
# but one hung ``lake`` cannot wedge a worker indefinitely.
DEFAULT_TIMEOUT_S = 1800


@dataclass(frozen=True)
class AxiomFinding:
    decl: str
    axiom: str
    file: str = ""

    @property
    def is_sorry(self) -> bool:
        # Lean's ``sorry`` elaborates to the ``sorryAx`` axiom.
        return self.axiom.lower().startswith("sorryax")


@dataclass
class AxiomSweepReport:
    findings: list[AxiomFinding] = field(default_factory=list)
    files_checked: int = 0
    ran: bool = False
    error: str | None = None
    duration_s: int = 0

    jobs: int = 1
    scope: str = "full"
    target_files: list[str] = field(default_factory=list)
    failed_files: list[str] = field(default_factory=list)

    @property
    def sorry_launderings(self) -> list[AxiomFinding]:
        """Findings that depend on ``sorryAx`` — the laundering signal."""
        return [f for f in self.findings if f.is_sorry]

    @property
    def other_axioms(self) -> list[AxiomFinding]:
        return [f for f in self.findings if not f.is_sorry]

    @property
    def has_launderings(self) -> bool:
        return bool(self.sorry_launderings)


def _script_path() -> Path:
    """Locate the bundled ``check_axioms_inline.sh`` regardless of layout."""
    from archon.commands.init.utils import data_path
    return data_path("skills/lean4/lib/scripts/check_axioms_inline.sh")


@dataclass(frozen=True)
class _AxiomFileResult:
    rel: str
    findings: tuple[AxiomFinding, ...] = ()
    files_checked: int = 0
    error: str = ""


def _relative(path: Path, project_path: Path) -> str:
    try:
        return path.resolve().relative_to(project_path.resolve()).as_posix()
    except (OSError, ValueError):
        return str(path)


def _project_lean_files(project_path: Path) -> list[Path]:
    """Return source Lean files, excluding caches and Archon runtime copies."""
    files: list[Path] = []
    for path in project_path.rglob("*.lean"):
        try:
            rel = path.resolve().relative_to(project_path.resolve())
        except (OSError, ValueError):
            continue
        if any(part.startswith(".") for part in rel.parts[:-1]):
            continue
        files.append(path.resolve())
    return sorted(set(files), key=lambda path: _relative(path, project_path))


def _normalize_targets(
    project_path: Path,
    targets: Iterable[Path] | None,
) -> list[Path]:
    if targets is None:
        return _project_lean_files(project_path)
    normalized: dict[str, Path] = {}
    root = project_path.resolve()
    for raw in targets:
        try:
            path = Path(raw).resolve()
            path.relative_to(root)
        except (OSError, ValueError):
            continue
        if path.is_file() and path.suffix == ".lean":
            normalized[_relative(path, project_path)] = path
    return [normalized[key] for key in sorted(normalized)]


def _run_isolated_axiom_check(
    *,
    project_path: Path,
    source: Path,
    script: Path,
    scratch_root: Path,
    timeout_s: int,
) -> _AxiomFileResult:
    """Run the mutating shell checker against a private disposable copy."""
    rel = _relative(source, project_path)
    try:
        with tempfile.TemporaryDirectory(
            prefix="target-", dir=scratch_root,
        ) as temp_dir:
            probe = Path(temp_dir) / source.name
            shutil.copy2(source, probe)
            result = subprocess.run(
                ["bash", str(script), str(probe), "--report-only"],
                cwd=project_path,
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
    except subprocess.TimeoutExpired:
        return _AxiomFileResult(
            rel=rel, error=f"timed out after {timeout_s}s",
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return _AxiomFileResult(
            rel=rel, error=f"{type(exc).__name__}: {exc}",
        )

    clean = _ANSI_RE.sub("", result.stdout or "")
    findings = tuple(
        AxiomFinding(
            decl=match.group("decl"),
            axiom=match.group("axiom"),
            file=rel,
        )
        for match in _FINDING_RE.finditer(clean)
    )
    files_checked = sum(
        1 for line in clean.splitlines() if line.startswith("File:")
    )
    if result.returncode != 0:
        details = ((result.stderr or "") + "\n" + clean).strip()
        return _AxiomFileResult(
            rel=rel,
            findings=findings,
            files_checked=files_checked,
            error=(
                f"checker exited {result.returncode}: "
                f"{details[-600:] or 'no diagnostics'}"
            ),
        )
    return _AxiomFileResult(
        rel=rel,
        findings=findings,
        files_checked=files_checked,
    )


def run_axiom_sweep(
    project_path: Path,
    *,
    timeout_s: int = DEFAULT_TIMEOUT_S,
    targets: Iterable[Path] | None = None,
    jobs: int = 1,
    scratch_root: Path | None = None,
    worker_fn: Callable[..., _AxiomFileResult] = _run_isolated_axiom_check,
    executor_factory=ThreadPoolExecutor,
) -> AxiomSweepReport | None:
    """Run the axiom sweep over ``project_path``.

    Returns ``None`` when there's nothing to check (no Lean project /
    script missing) so the caller can silently skip. Explicit ``targets``
    request an incremental sweep; ``None`` requests a full source scan.
    """
    has_lake = any(
        (project_path / name).exists()
        for name in ("lakefile.lean", "lakefile.toml")
    )
    if not has_lake:
        return None

    script = _script_path()
    if not script.exists():
        log.warn(f"check_axioms_inline.sh not found at {script}")
        return None

    selected = _normalize_targets(project_path, targets)
    scope = "full" if targets is None else "current-objectives"
    workers = max(1, min(int(jobs), len(selected) or 1))
    scratch = (
        scratch_root
        if scratch_root is not None
        else project_path / ".archon" / "tmp" / "axiom-sweep"
    )
    scratch.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    by_rel: dict[str, _AxiomFileResult] = {}
    with executor_factory(max_workers=workers) as pool:
        pending = {
            pool.submit(
                worker_fn,
                project_path=project_path,
                source=source,
                script=script,
                scratch_root=scratch,
                timeout_s=timeout_s,
            ): _relative(source, project_path)
            for source in selected
        }
        for future in as_completed(pending):
            rel = pending[future]
            try:
                by_rel[rel] = future.result()
            except Exception as exc:
                by_rel[rel] = _AxiomFileResult(
                    rel=rel, error=f"{type(exc).__name__}: {exc}",
                )

    ordered = [by_rel[_relative(path, project_path)] for path in selected]
    findings = [
        finding for result in ordered for finding in result.findings
    ]
    failures = [result.rel for result in ordered if result.error]
    errors = [
        f"{result.rel}: {result.error}" for result in ordered if result.error
    ]
    secs = int(time.monotonic() - start)
    return AxiomSweepReport(
        findings=findings,
        files_checked=sum(result.files_checked for result in ordered),
        ran=not failures,
        error="; ".join(errors)[:4000] or None,
        duration_s=secs,
        jobs=workers,
        scope=scope,
        target_files=[_relative(path, project_path) for path in selected],
        failed_files=failures,
    )


def write_reports(
    report: AxiomSweepReport,
    iter_log_dir: Path,
    project_path: Path,
) -> tuple[Path, Path]:
    """Write ``axiom-sweep.{json,md}`` to ``iter_log_dir``.

    Returns ``(json_path, md_path)``.
    """
    import json

    json_path = iter_log_dir / "axiom-sweep.json"
    md_path = iter_log_dir / "axiom-sweep.md"

    payload = {
        "ran": report.ran,
        "error": report.error,
        "filesChecked": report.files_checked,
        "durationSecs": report.duration_s,
        "jobs": report.jobs,
        "scope": report.scope,
        "targetFiles": report.target_files,
        "failedFiles": report.failed_files,
        "sorryLaunderings": [
            {"decl": f.decl, "axiom": f.axiom, "file": f.file}
            for f in report.sorry_launderings
        ],
        "otherNonStandardAxioms": [
            {"decl": f.decl, "axiom": f.axiom, "file": f.file}
            for f in report.other_axioms
        ],
    }
    json_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    lines = [
        "# Axiom sweep",
        "",
        f"- Scope: {report.scope}",
        f"- Jobs: {report.jobs}",
        f"- Selected targets: {len(report.target_files)}",
        "",
    ]
    if not report.ran:
        lines += [f"Sweep did not complete: {report.error or 'unknown error'}.", ""]
    else:
        lines.append(
            f"Checked {report.files_checked} file(s) in {report.duration_s}s."
        )
        lines.append("")
        if report.has_launderings:
            lines += [
                "## ⚠ sorryAx laundering",
                "",
                "These declarations compile without a `sorry` warning but "
                "depend on `sorryAx` (a `sorry` reached through a clean-"
                "compiling delegate). The warning-based sorry count does "
                "NOT see them — treat them as open sorries.",
                "",
            ]
            for f in report.sorry_launderings:
                where = f" in `{f.file}`" if f.file else ""
                lines.append(
                    f"- `{f.decl}`{where} — depends on `{f.axiom}`"
                )
            lines.append("")
        else:
            lines += ["No `sorryAx` laundering detected.", ""]
        if report.other_axioms:
            lines += ["## Other non-standard axioms", ""]
            for f in report.other_axioms:
                where = f" in `{f.file}`" if f.file else ""
                lines.append(f"- `{f.decl}`{where} — `{f.axiom}`")
            lines.append("")
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return json_path, md_path
