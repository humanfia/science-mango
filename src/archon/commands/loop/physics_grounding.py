"""Deterministic LeanExplore grounding reports for physics targets.

Physics formalization agents are asked to use LeanExplore and record the
queries they used, but that alone is too easy to miss. This module provides a
loop-owned preflight that searches LeanExplore for the physics blueprint target
before autoformalization/proving and writes a reviewable task_results report.
"""

from __future__ import annotations

import asyncio
import hashlib
import os
import re
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Iterable


PHYSICS_MARKER = "% archon:physics"
COVERS_RE = re.compile(r"^\s*%\s*archon:covers\s+(.+?)\s*$", re.MULTILINE)
TITLE_RE = re.compile(
    r"\\begin\{(?:definition|lemma|theorem|proposition)\}(?:\[(.*?)\])?",
    re.DOTALL,
)
LEAN_RE = re.compile(r"\\lean\{([^}]+)\}")

FALLBACK_QUERIES = (
    "Electromagnetism.ElectricField",
    "Electromagnetism.ChargeDensity",
    "Real.sqrt square root",
    "derivative at a point",
    "MeasureTheory integral",
    "Constants.kB Boltzmann constant",
)


@dataclass(frozen=True)
class GroundingCandidate:
    """A compact LeanExplore result recorded in task_results."""

    name: str
    module: str = ""
    docstring: str | None = None
    source_text: str | None = None
    source_link: str | None = None
    informalization: str | None = None

    @property
    def package(self) -> str:
        hay = " ".join(
            x or "" for x in (self.name, self.module, self.source_link)
        ).lower()
        if "physlean" in hay or "physlib" in hay:
            return "PhysLean"
        if "mathlib" in hay:
            return "Mathlib"
        return "unknown"


@dataclass
class QueryEvidence:
    """Search evidence for one query."""

    query: str
    candidates: list[GroundingCandidate] = field(default_factory=list)
    error: str | None = None


@dataclass
class PhysicsGroundingReport:
    """One generated grounding report."""

    lean_file: Path
    chapter: Path
    report_path: Path
    status: str
    query_evidence: list[QueryEvidence]
    local_abstractions: list[str] = field(default_factory=list)
    grounding_gaps: list[str] = field(default_factory=list)
    cached: bool = False

    @property
    def is_complete(self) -> bool:
        return self.status == "complete"


SearchFn = Callable[[str, list[str], int], list[GroundingCandidate]]
GROUNDING_BACKENDS = frozenset({"auto", "api", "local"})


def physics_chapter_targets(
    project_path: Path,
    *,
    lean_files: Iterable[Path] | None = None,
) -> list[tuple[Path, Path]]:
    """Return ``(chapter, lean_file)`` pairs for live physics chapters.

    When ``lean_files`` is provided, only chapters covering those objectives
    are returned. An empty iterable deliberately means no targets.
    """
    chapters_dir = project_path / "blueprint" / "src" / "chapters"
    if not chapters_dir.is_dir():
        return []

    objective_files = (
        {Path(path).resolve() for path in lean_files}
        if lean_files is not None
        else None
    )
    pairs: list[tuple[Path, Path]] = []
    seen: set[Path] = set()
    for chapter in sorted(chapters_dir.glob("*.tex")):
        try:
            text = chapter.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if PHYSICS_MARKER not in text:
            continue
        covers = [m.group(1).strip() for m in COVERS_RE.finditer(text)]
        if not covers:
            conventional = project_path / f"{chapter.stem}.lean"
            covers = [conventional.name]
        for raw in covers:
            lean_file = (project_path / raw).resolve()
            if objective_files is not None and lean_file not in objective_files:
                continue
            if lean_file in seen:
                continue
            seen.add(lean_file)
            pairs.append((chapter, lean_file))
    return pairs


def _clean_latex_text(text: str) -> str:
    text = re.sub(r"\\[a-zA-Z]+\*?(?:\[[^\]]*\])?(?:\{([^{}]*)\})?", r" \1 ", text)
    text = re.sub(r"[$\\{}_^]", " ", text)
    return " ".join(text.split())


def _blueprint_queries(chapter: Path, *, max_queries: int = 10) -> list[str]:
    """Derive concise LeanExplore queries from a physics blueprint chapter."""
    try:
        text = chapter.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return []

    queries: list[str] = []

    # Prioritize physical concepts over theorem titles. Titles such as
    # "Ring figure geometry" otherwise bias LeanExplore toward algebraic rings
    # before the search ever reaches the actual electric-field content.
    lower = text.lower()
    concept_seeds = [
        ("electric field", "electric field"),
        ("charged ring", "electric field charged ring"),
        ("charge density", "electric charge density"),
        ("linear charge", "linear charge density"),
        ("charge", "electric charge"),
        ("permittivity", "electric permittivity"),
        ("coulomb", "Coulomb law electric field"),
        ("gauss", "Gauss law divergence electric field"),
        ("divergence", "divergence vector field"),
        ("harmonic", "harmonic oscillator angular frequency"),
        ("sqrt", "Real.sqrt square root"),
        ("derivative", "derivative at a point"),
        ("euclidean", "EuclideanSpace vector components"),
    ]
    for needle, query in concept_seeds:
        if needle in lower:
            queries.append(query)

    for title in TITLE_RE.findall(text):
        cleaned = _clean_latex_text(title or "")
        if cleaned and cleaned.lower() not in {"proof"}:
            queries.append(cleaned)

    for lean_name in LEAN_RE.findall(text):
        tail = lean_name.rsplit(".", 1)[-1]
        words = re.sub(r"([a-z])([A-Z])", r"\1 \2", tail).replace("_", " ")
        words = " ".join(words.split())
        if words:
            queries.append(words)

    out: list[str] = []
    seen: set[str] = set()
    for q in queries:
        q = " ".join(q.split())
        if len(q) < 3:
            continue
        key = q.lower()
        if key in seen:
            continue
        seen.add(key)
        out.append(q)
        if len(out) >= max_queries:
            break
    return out


def _candidate_from_result(result: object) -> GroundingCandidate:
    return GroundingCandidate(
        name=str(getattr(result, "name", "") or ""),
        module=str(getattr(result, "module", "") or ""),
        docstring=getattr(result, "docstring", None),
        source_text=getattr(result, "source_text", None),
        source_link=getattr(result, "source_link", None),
        informalization=getattr(result, "informalization", None),
    )


async def _api_search_once(
    query: str,
    packages: list[str],
    limit: int,
    *,
    api_key: str,
    timeout: float,
) -> list[GroundingCandidate]:
    from lean_explore.api import ApiClient

    client = ApiClient(api_key=api_key, timeout=timeout)
    response = await client.search(query=query, limit=limit, packages=packages)
    return [_candidate_from_result(item) for item in response.results[:limit]]


def _api_searcher(
    *,
    api_key: str,
    timeout: float,
) -> SearchFn:
    def search(query: str, packages: list[str], limit: int) -> list[GroundingCandidate]:
        return asyncio.run(
            _api_search_once(
                query,
                packages,
                limit,
                api_key=api_key,
                timeout=timeout,
            )
        )

    return search


class _LocalSearcher:
    """Synchronous adapter around one reusable LeanExplore local service."""

    def __init__(self) -> None:
        from importlib.util import find_spec

        missing = [
            name
            for name in ("torch", "sentence_transformers")
            if find_spec(name) is None
        ]
        if missing:
            joined = ", ".join(missing)
            raise RuntimeError(
                f"LeanExplore local runtime dependencies are missing: {joined}. "
                "Install the `lean-explore[local]` extra."
            )

        from lean_explore.search import SearchEngine, Service

        self._service = Service(engine=SearchEngine(use_local_data=False))
        self._loop = asyncio.new_event_loop()

    def __call__(
        self,
        query: str,
        packages: list[str],
        limit: int,
    ) -> list[GroundingCandidate]:
        response = self._loop.run_until_complete(
            self._service.search(
                query=query,
                limit=limit,
                rerank_top=0,
                packages=packages,
            )
        )
        return [_candidate_from_result(item) for item in response.results[:limit]]

    def close(self) -> None:
        try:
            engine = self._service.engine.engine
            self._loop.run_until_complete(engine.dispose())
        finally:
            self._loop.close()


def _local_searcher() -> SearchFn:
    """Build a local LeanExplore searcher from fetched cache data."""
    return _LocalSearcher()


def _resolve_searcher(
    *,
    backend: str,
    api_key: str | None,
    timeout: float,
    searcher: SearchFn | None,
) -> tuple[SearchFn | None, str, str | None, bool]:
    """Resolve a grounding backend and return searcher/backend/error/ownership."""
    normalized = backend.lower().strip()
    if normalized not in GROUNDING_BACKENDS:
        supported = ", ".join(sorted(GROUNDING_BACKENDS))
        raise ValueError(f"LeanExplore grounding backend must be one of: {supported}")
    if searcher is not None:
        return searcher, "custom", None, False
    if normalized == "api":
        if not api_key:
            return (
                None,
                "api",
                "LEANEXPLORE_API_KEY is missing, so LeanExplore API search did not run.",
                False,
            )
        return _api_searcher(api_key=api_key, timeout=timeout), "api", None, False

    if normalized == "auto" and api_key:
        return _api_searcher(api_key=api_key, timeout=timeout), "api", None, False

    try:
        return _local_searcher(), "local", None, True
    except Exception as exc:
        prefix = "LeanExplore local backend is unavailable"
        suffix = "Run `lean-explore data fetch` to install its local index."
        if normalized == "auto":
            prefix += " and LEANEXPLORE_API_KEY is not set"
        return None, "local", f"{prefix}: {exc}. {suffix}", False


def _summarize_local_abstractions(chapter: Path) -> list[str]:
    """Extract likely local abstraction names from the blueprint's Lean refs."""
    try:
        text = chapter.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return []
    names = []
    for lean_name in LEAN_RE.findall(text):
        if "." in lean_name:
            tail = lean_name.rsplit(".", 1)[-1]
        else:
            tail = lean_name
        if tail and tail[:1].isupper():
            names.append(lean_name)
    return sorted(set(names))


def _report_name(project_path: Path, lean_file: Path) -> str:
    try:
        rel = lean_file.resolve().relative_to(project_path.resolve())
    except ValueError:
        rel = Path(lean_file.name)
    rel_stem = rel.with_suffix("").as_posix().replace("/", "_")
    return f"physics-grounding-{Path(rel_stem).name}.md"


def _input_fingerprint(chapter: Path, lean_file: Path) -> str | None:
    """Hash grounding inputs so cache validity does not depend on mtimes."""
    digest = hashlib.sha256()
    try:
        digest.update(chapter.read_bytes())
        digest.update(b"\0archon-physics-grounding\0")
        if lean_file.is_file():
            digest.update(lean_file.read_bytes())
        else:
            digest.update(b"<missing-lean-file>")
    except OSError:
        return None
    return digest.hexdigest()


def _reuse_complete_report(
    project_path: Path,
    chapter: Path,
    lean_file: Path,
    report_path: Path,
    *,
    backend: str,
) -> PhysicsGroundingReport | None:
    """Reuse a complete report when neither of its inputs has changed."""
    try:
        text = report_path.read_text(encoding="utf-8")
    except OSError:
        return None

    fingerprint = _input_fingerprint(chapter, lean_file)
    if "- Grounding status: complete" not in text:
        return None
    if backend in {"api", "local"} and f"- Search backend: {backend}" not in text:
        return None
    if not fingerprint or f"- Input fingerprint: sha256:{fingerprint}" not in text:
        return None

    return PhysicsGroundingReport(
        lean_file=lean_file,
        chapter=chapter,
        report_path=report_path,
        status="complete",
        query_evidence=[],
        local_abstractions=_summarize_local_abstractions(chapter),
        cached=True,
    )


def _rel(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return str(path)


def _format_candidate(candidate: GroundingCandidate) -> str:
    bits = [f"`{candidate.name or '<unnamed>'}`"]
    if candidate.module:
        bits.append(f"module `{candidate.module}`")
    bits.append(f"package {candidate.package}")
    desc = candidate.docstring or candidate.informalization
    if desc:
        desc = " ".join(str(desc).split())
        if len(desc) > 220:
            desc = desc[:217].rstrip() + "..."
        bits.append(desc)
    return "- " + " | ".join(bits)


def _safe_failure_text(text: str) -> str:
    return re.sub(r"\berror\s*:", "error -", str(text), flags=re.IGNORECASE)


def _write_report(
    project_path: Path,
    chapter: Path,
    lean_file: Path,
    report_path: Path,
    evidence: list[QueryEvidence],
    *,
    backend: str,
    backend_error: str | None,
    packages: list[str],
) -> PhysicsGroundingReport:
    any_success = any(q.candidates for q in evidence)
    status = "complete" if any_success else "incomplete"
    local_abstractions = _summarize_local_abstractions(chapter)
    grounding_gaps: list[str] = []
    if backend_error:
        grounding_gaps.append(backend_error)
    for q in evidence:
        if q.error:
            grounding_gaps.append(f"`{q.query}` search unavailable: {_safe_failure_text(q.error)}")
        elif not q.candidates:
            grounding_gaps.append(f"`{q.query}` returned no candidates.")

    lines = [
        "# Physics LeanExplore Grounding Log",
        "",
        f"- Target Lean file: `{_rel(lean_file, project_path)}`",
        f"- Blueprint chapter: `{_rel(chapter, project_path)}`",
        f"- Grounding status: {status}",
        f"- Search backend: {backend}",
        f"- Input fingerprint: sha256:{_input_fingerprint(chapter, lean_file) or 'unavailable'}",
        f"- Packages searched: {', '.join(packages)}",
        "",
        "## LeanExplore queries/candidates actually used",
        "",
    ]
    if not evidence:
        lines.append("- No LeanExplore queries were derived from the blueprint.")
    for q in evidence:
        lines.append(f"### Query: `{q.query}`")
        if q.error:
            lines.append(f"- Search unavailable: {_safe_failure_text(q.error)}")
        elif not q.candidates:
            lines.append("- No candidates returned.")
        else:
            for candidate in q.candidates:
                lines.append(_format_candidate(candidate))
        lines.append("")

    grounded = []
    for q in evidence:
        for candidate in q.candidates:
            if candidate.name:
                grounded.append(candidate)
    lines += [
        "## Grounded Mathlib/PhysLean names",
        "",
    ]
    if grounded:
        for candidate in grounded:
            lines.append(f"- `{candidate.name}` ({candidate.package})")
    else:
        lines.append("- None yet.")

    lines += [
        "",
        "## Local abstractions introduced",
        "",
    ]
    if local_abstractions:
        for name in local_abstractions:
            lines.append(
                f"- `{name}`: blueprint-local physics/modeling abstraction; "
                "must preserve the physical role instead of erasing it to a bare scalar."
            )
    else:
        lines.append("- None detected from blueprint Lean references.")

    lines += [
        "",
        "## Grounding gaps",
        "",
    ]
    if grounding_gaps:
        for gap in grounding_gaps:
            lines.append(f"- {gap}")
    else:
        lines.append("- No unresolved LeanExplore grounding gaps were recorded by this preflight.")

    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return PhysicsGroundingReport(
        lean_file=lean_file,
        chapter=chapter,
        report_path=report_path,
        status=status,
        query_evidence=evidence,
        local_abstractions=local_abstractions,
        grounding_gaps=grounding_gaps,
    )


def _search_with_retries(
    searcher: SearchFn,
    query: str,
    packages: list[str],
    limit: int,
    *,
    max_attempts: int,
    retry_delay: float,
) -> QueryEvidence:
    last_error: str | None = None
    attempts = max(1, max_attempts)
    for attempt in range(attempts):
        try:
            return QueryEvidence(
                query=query,
                candidates=searcher(query, packages, limit),
            )
        except Exception as exc:  # defensive: record evidence, do not crash loop
            last_error = str(exc)
            if attempt + 1 < attempts and retry_delay > 0:
                time.sleep(retry_delay)
    return QueryEvidence(query=query, error=last_error or "LeanExplore search failed.")


def run_physics_grounding(
    project_path: Path,
    *,
    limit: int = 3,
    max_queries: int = 10,
    api_key: str | None = None,
    backend: str = "auto",
    packages: Iterable[str] = ("Mathlib", "Physlib"),
    timeout: float = 20.0,
    max_attempts: int = 3,
    retry_delay: float = 0.25,
    searcher: SearchFn | None = None,
    lean_files: Iterable[Path] | None = None,
    reuse_unchanged: bool = True,
) -> list[PhysicsGroundingReport]:
    """Generate task_results grounding logs for selected physics targets."""
    project_path = project_path.resolve()
    state_dir = project_path / ".archon"
    task_results = state_dir / "task_results"
    package_list = list(packages)
    targets = physics_chapter_targets(project_path, lean_files=lean_files)

    reports: list[PhysicsGroundingReport] = []
    pending: list[tuple[Path, Path, Path]] = []
    for chapter, lean_file in targets:
        report_path = task_results / _report_name(project_path, lean_file)
        cached_report = (
            _reuse_complete_report(
                project_path,
                chapter,
                lean_file,
                report_path,
                backend=backend,
            )
            if reuse_unchanged
            else None
        )
        if cached_report is not None:
            reports.append(cached_report)
        else:
            pending.append((chapter, lean_file, report_path))

    # Avoid loading the local embedding model when every selected report is
    # already current (or when the current batch contains no physics targets).
    if not pending:
        return reports

    api_key = api_key if api_key is not None else os.environ.get("LEANEXPLORE_API_KEY")
    real_searcher, resolved_backend, backend_error, owns_searcher = _resolve_searcher(
        backend=backend,
        api_key=api_key,
        timeout=timeout,
        searcher=searcher,
    )

    try:
        for chapter, lean_file, report_path in pending:
            queries = _blueprint_queries(chapter, max_queries=max_queries)
            evidence: list[QueryEvidence] = []
            searched: set[str] = set()
            for query in queries:
                searched.add(query.lower())
                if real_searcher is None:
                    evidence.append(
                        QueryEvidence(
                            query=query,
                            error=backend_error or "LeanExplore searcher is unavailable.",
                        )
                    )
                    continue
                evidence.append(
                    _search_with_retries(
                        real_searcher,
                        query,
                        package_list,
                        limit,
                        max_attempts=max_attempts,
                        retry_delay=retry_delay,
                    )
                )

            if real_searcher is not None and not any(q.candidates for q in evidence):
                for query in FALLBACK_QUERIES:
                    if query.lower() in searched:
                        continue
                    evidence.append(
                        _search_with_retries(
                            real_searcher,
                            query,
                            package_list,
                            limit,
                            max_attempts=max_attempts,
                            retry_delay=retry_delay,
                        )
                    )
                    if evidence[-1].candidates:
                        break

            reports.append(
                _write_report(
                    project_path,
                    chapter,
                    lean_file,
                    report_path,
                    evidence,
                    backend=resolved_backend,
                    backend_error=backend_error,
                    packages=package_list,
                )
            )
    finally:
        closer = getattr(real_searcher, "close", None)
        if owns_searcher and callable(closer):
            closer()
    return reports
