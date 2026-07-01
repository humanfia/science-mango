"""Problem-level formalization contract extraction for physics tasks."""

from __future__ import annotations

import re


def _sentences(text: str) -> list[str]:
    return [
        part.strip()
        for part in re.split(r"(?<=[.!?。])\s+", text or "")
        if part.strip()
    ]


def _backtick_identifiers(text: str) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for match in re.finditer(r"`([^`]+)`", text or ""):
        ident = match.group(1).strip()
        if ident and ident not in seen:
            seen.add(ident)
            out.append(ident)
    return out


def build_problem_contract(problem_text: str, max_problem_chars: int = 1200) -> str:
    """Build a compact, prompt-ready contract from the root problem statement.

    This is intentionally heuristic and domain-general: it does not encode
    per-problem special cases. Its job is to preserve explicit abstraction
    constraints from the original task so later node-level calls do not infer
    lower-level mechanisms that the problem excluded.
    """

    text = " ".join((problem_text or "").split())
    if not text:
        return "No explicit problem-level contract was provided."

    lower = text.lower()
    measured_sentences = [
        s
        for s in _sentences(text)
        if any(
            marker in s.lower()
            for marker in (
                "measured",
                "readout",
                "raw measurement",
                "data-reduction",
                "data reduction",
                "calibrated",
                "treat ",
            )
        )
        and any(
            scalar_marker in s.lower()
            for scalar_marker in ("scalar", "quantity", "observable", "reading", "slope")
        )
    ]
    forbidden_sentences = [
        s
        for s in _sentences(text)
        if any(
            marker in s.lower()
            for marker in (
                "do not formalize",
                "do not model",
                "do not introduce",
                "not as",
                "rather than",
                "without deriving",
            )
        )
    ]

    identifiers = _backtick_identifiers(text)
    lines = [
        "[Problem-level formalization contract]",
        "Use this contract when deciding whether a concept is a leaf and when generating Lean code.",
        f"Original problem excerpt: {text[:max_problem_chars]}",
    ]

    if measured_sentences or identifiers:
        lines.append(
            "Measured/readout/scalar observables and final-target quantities should usually remain leaf-level variables or lightweight context unless the problem explicitly asks for their physical mechanism."
        )
        for sentence in measured_sentences[:5]:
            lines.append(f"- Measured/context clue: {sentence}")
        if identifiers:
            lines.append(
                "- Explicit identifiers from the problem: " + ", ".join(identifiers[:20])
            )

    if forbidden_sentences:
        lines.append(
            "Do not introduce out-of-scope mechanisms that the problem explicitly excludes or that are lower-level than the stated formalization target."
        )
        for sentence in forbidden_sentences[:5]:
            lines.append(f"- Out-of-scope clue: {sentence}")

    if not measured_sentences and not forbidden_sentences:
        lines.append(
            "No explicit measured-scalar or excluded-mechanism clue was detected; use normal physics granularity."
        )

    if "derivative" in lower or "differential" in lower or "d/d" in lower:
        lines.append(
            "- Calculus caution: introduce derivative operators only if the target requires proving analytic differentiation, not when a slope/rate is given as measured data."
        )

    return "\n".join(lines)
