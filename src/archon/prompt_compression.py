"""Deterministic prompt compression for Archon phase prompts.

The compressor is intentionally extractive: it shortens large dynamic
context sections while leaving phase rules and safety instructions intact.
This makes it suitable for ablation runs where the only intended variable is
how much historical/runtime context the plan and review agents receive.
"""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path


_HEADING_RE = re.compile(r"(?m)^[ \t]*##\s+(.+?)\s*$")

_COMPRESSIBLE_PREFIXES: dict[str, tuple[str, ...]] = {
    "plan": (
        "User hints",
        "Automated validation notes",
        "Archon memory",
        "Blueprint doctor",
        "Axiom sweep",
        "Blueprint graph state",
        "Peer projects",
        "References available",
        "Per-iteration sidecars",
        "Recent",
    ),
    "review": (
        "Archon memory",
        "Per-iteration sidecars",
        "Recent",
        "Blueprint doctor report",
    ),
}

_PROTECTED_PREFIXES: tuple[str, ...] = (
    "Available subagents",
    "Available prover modes",
    "Physics review requirements",
    "Physics-aware typed blueprint policy",
    "Protected by the mathematician",
    "Developer feedback channel",
    "`\\leanok` sync attribution",
)
_PROTECTED_EXACT_TITLES: tuple[str, ...] = ("Blueprint",)

_IMPORTANT_LINE_RE = re.compile(
    r"("
    r"\b(blocker|blocked|critical|fatal|error|failed|failure|warn|warning)\b|"
    r"\b(sorry|axiom|leanok|mathlibok|LeanExplore|grounding|physics)\b|"
    r"\b(PROGRESS|STRATEGY|PROJECT_STATUS|task_results|AUTO_NOTES)\b|"
    r"\.(lean|tex|md|json|jsonl)\b|"
    r"`[^`]+`"
    r")",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class PromptCompressionConfig:
    """Runtime knobs for plan/review prompt compression."""

    enabled: bool = False
    target_chars: int = 40000
    section_chars: int = 6000
    min_section_chars: int = 1200
    lead_lines: int = 10


@dataclass(frozen=True)
class SectionCompressionStats:
    title: str
    original_chars: int
    compressed_chars: int
    omitted_chars: int
    omitted_lines: int


@dataclass(frozen=True)
class PromptCompressionReport:
    role: str
    enabled: bool
    changed: bool
    original_chars: int
    compressed_chars: int
    omitted_chars: int
    target_chars: int
    section_chars: int
    created_at: str
    sections: tuple[SectionCompressionStats, ...]

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass(frozen=True)
class PromptCompressionResult:
    prompt: str
    report: PromptCompressionReport


def _utcnow_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _normalize_title(title: str) -> str:
    return " ".join(title.strip().split())


def _starts_with_any(title: str, prefixes: tuple[str, ...]) -> bool:
    normalized = _normalize_title(title).lower()
    return any(normalized.startswith(prefix.lower()) for prefix in prefixes)


def _section_title(section: str) -> str:
    first = section.splitlines()[0] if section.splitlines() else ""
    return first.lstrip().lstrip("#").strip()


def _is_protected_title(title: str) -> bool:
    normalized = _normalize_title(title).lower()
    if any(normalized == exact.lower() for exact in _PROTECTED_EXACT_TITLES):
        return True
    return _starts_with_any(title, _PROTECTED_PREFIXES)


def _should_compress(role: str, title: str, section_len: int, cfg: PromptCompressionConfig) -> bool:
    if section_len <= cfg.section_chars:
        return False
    if _is_protected_title(title):
        return False
    prefixes = _COMPRESSIBLE_PREFIXES.get(role, ())
    if _starts_with_any(title, prefixes):
        return True
    # Unknown large sections are left alone unless they are very large. This
    # avoids compressing role rules while still bounding accidental huge
    # injected state blocks.
    return section_len > cfg.section_chars * 2


def _trim_line(line: str, *, max_chars: int = 420) -> str:
    if len(line) <= max_chars:
        return line
    return line[: max_chars - 18].rstrip() + " ... [trimmed]"


def _add_unique_line(out: list[str], seen: set[str], line: str) -> None:
    stripped = line.rstrip()
    if not stripped:
        return
    key = " ".join(stripped.split())
    if key in seen:
        return
    seen.add(key)
    out.append(_trim_line(stripped))


def _compress_section(section: str, *, role: str, cfg: PromptCompressionConfig) -> tuple[str, SectionCompressionStats | None]:
    title = _section_title(section)
    original_len = len(section)
    if not _should_compress(role, title, original_len, cfg):
        return section, None

    lines = section.splitlines()
    heading = lines[0] if lines else f"## {title}"
    body_lines = lines[1:]
    budget = max(cfg.min_section_chars, cfg.section_chars)

    lead: list[str] = []
    seen: set[str] = set()
    for line in body_lines:
        if len(lead) >= cfg.lead_lines:
            break
        _add_unique_line(lead, seen, line)

    important: list[str] = []
    bullets: list[str] = []
    for line in body_lines:
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith(("```", "<!--")):
            continue
        if _IMPORTANT_LINE_RE.search(stripped):
            _add_unique_line(important, seen, line)
        elif stripped.startswith(("- ", "* ", "1. ", "2. ", "3. ", "4. ", "5. ")):
            _add_unique_line(bullets, seen, line)

    compressed_lines = [
        heading,
        "",
        (
            "[ARCHON PROMPT COMPRESSION] This dynamic context section was "
            "shortened deterministically. Read the referenced files if exact "
            "detail is needed."
        ),
        f"Original section chars: {original_len}; target section chars: {budget}.",
        "",
    ]
    if lead:
        compressed_lines += ["### Preserved opening context", *lead, ""]
    if important:
        compressed_lines += ["### High-signal extracted lines", *important, ""]
    if bullets:
        compressed_lines += ["### Additional retained bullets", *bullets, ""]

    compressed = "\n".join(compressed_lines).rstrip() + "\n"
    if len(compressed) > budget:
        compressed = compressed[:budget].rstrip()
        compressed += "\n\n... [prompt compression truncated this section]\n"

    # Do not replace a section unless the compression materially helps.
    if len(compressed) >= int(original_len * 0.95):
        return section, None

    compressed_lines_count = len(compressed.splitlines())
    stats = SectionCompressionStats(
        title=title,
        original_chars=original_len,
        compressed_chars=len(compressed),
        omitted_chars=max(0, original_len - len(compressed)),
        omitted_lines=max(0, len(lines) - compressed_lines_count),
    )
    return compressed, stats


def compress_prompt(
    prompt: str,
    *,
    role: str,
    config: PromptCompressionConfig,
) -> PromptCompressionResult:
    """Return a possibly compressed prompt plus a machine-readable report."""

    original_len = len(prompt)
    if not config.enabled:
        report = PromptCompressionReport(
            role=role,
            enabled=False,
            changed=False,
            original_chars=original_len,
            compressed_chars=original_len,
            omitted_chars=0,
            target_chars=config.target_chars,
            section_chars=config.section_chars,
            created_at=_utcnow_iso(),
            sections=(),
        )
        return PromptCompressionResult(prompt=prompt, report=report)

    matches = list(_HEADING_RE.finditer(prompt))
    if not matches:
        report = PromptCompressionReport(
            role=role,
            enabled=True,
            changed=False,
            original_chars=original_len,
            compressed_chars=original_len,
            omitted_chars=0,
            target_chars=config.target_chars,
            section_chars=config.section_chars,
            created_at=_utcnow_iso(),
            sections=(),
        )
        return PromptCompressionResult(prompt=prompt, report=report)

    effective_cfg = config
    if config.target_chars > 0 and original_len > config.target_chars:
        eligible_count = max(1, len(matches))
        dynamic_section = max(
            config.min_section_chars,
            min(config.section_chars, config.target_chars // eligible_count),
        )
        effective_cfg = PromptCompressionConfig(
            enabled=True,
            target_chars=config.target_chars,
            section_chars=dynamic_section,
            min_section_chars=config.min_section_chars,
            lead_lines=config.lead_lines,
        )

    chunks: list[str] = []
    stats: list[SectionCompressionStats] = []
    chunks.append(prompt[: matches[0].start()])
    for idx, match in enumerate(matches):
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(prompt)
        section = prompt[match.start():end]
        compressed, section_stats = _compress_section(
            section,
            role=role,
            cfg=effective_cfg,
        )
        chunks.append(compressed)
        if section_stats is not None:
            stats.append(section_stats)

    compressed_prompt = "".join(chunks)
    changed = compressed_prompt != prompt
    report = PromptCompressionReport(
        role=role,
        enabled=True,
        changed=changed,
        original_chars=original_len,
        compressed_chars=len(compressed_prompt),
        omitted_chars=max(0, original_len - len(compressed_prompt)),
        target_chars=config.target_chars,
        section_chars=effective_cfg.section_chars,
        created_at=_utcnow_iso(),
        sections=tuple(stats),
    )
    return PromptCompressionResult(prompt=compressed_prompt, report=report)


def write_prompt_compression_report(path: Path, report: PromptCompressionReport) -> None:
    """Write a compression report sidecar. Best-effort callers may catch OSError."""

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(report.to_dict(), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
