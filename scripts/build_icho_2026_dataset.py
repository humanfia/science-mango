#!/usr/bin/env python3
"""Build IChO 2026 data in the IPhO/HiPhO-compatible repository format.

The checked-in text files are deterministic PyMuPDF extractions from the four
English PDFs in ``icho_2026_source/raw``.  This builder performs no OCR and has
no third-party runtime dependencies.  It locates every numbered subquestion,
keeps the official question-page image as primary visual evidence, extracts
the official solution/rubric text, and emits both provenance-rich and strict
29-field Archon JSONL files.

Graphical structures, ticks, tables, and equations are not always represented
in PDF plain text.  Such rows retain an explicit visual-answer notice and a
page-level solution provenance pointer; selected experimental graphical
answers are also transcribed in ``ANSWER_OVERRIDES`` below.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "icho_2026_source"
RAW = SOURCE / "raw"
TEXT = SOURCE / "text"
IMAGE = SOURCE / "image"
PROCESSED = SOURCE / "processed"
REVIEW = SOURCE / "review"

HIPHO_REFERENCE = (
    ROOT
    / "hipho_ipho_2024_2025"
    / "hipho_ipho_2024_2025_archon.jsonl"
)

OFFICIAL_MATERIALS_URL = "https://www.icho2026.uz/problems"
MIRROR_INDEX_URL = (
    "https://scheikundeolympiade.science.ru.nl/internationaal/2026/index.html"
)

SOURCE_URLS = {
    "theory_problem.pdf": (
        "https://scheikundeolympiade.science.ru.nl/internationaal/2026/"
        "IChO2026%20Theory%20task%20final%20English.pdf"
    ),
    "theory_solution.pdf": (
        "https://scheikundeolympiade.science.ru.nl/internationaal/2026/"
        "IChO2026%20Theory%20Solutions.pdf"
    ),
    "experiment_problem.pdf": (
        "https://scheikundeolympiade.science.ru.nl/internationaal/2026/"
        "IChO2026%20exam-Experiment-full-Engels.pdf"
    ),
    "experiment_solution.pdf": (
        "https://scheikundeolympiade.science.ru.nl/internationaal/2026/"
        "IChO2026%20exam-Experiment-Solutions-full-Engels.pdf"
    ),
}

ARCHON_SCHEMA_FIELDS = (
    "index",
    "category",
    "source_dataset",
    "source_dataset_url",
    "year",
    "problem_id",
    "problem_number",
    "part_id",
    "part_letter",
    "subquestion_number",
    "formalization_input_policy",
    "context",
    "current_question",
    "question",
    "answer",
    "answers",
    "marking",
    "answer_type",
    "unit",
    "points",
    "modality",
    "field",
    "source",
    "previous_parts",
    "previous_part_count",
    "images",
    "image",
    "image_count",
    "raw_hipho_image_question",
)

NATIVE_SCHEMA_FIELDS = (
    "id",
    "index",
    "source_index",
    "problem_id",
    "part_id",
    "question",
    "current_question",
    "shared_context",
    "answer",
    "category",
    "dataset",
    "dataset_format",
    "points",
    "paper",
    "kind",
    "formalization_ready",
    "image",
    "images",
    "previous_parts",
    "source_pdf",
    "source_page",
    "printed_page",
    "solution_pdf",
    "marking_scheme_pdf",
    "source_url",
    "solution_url",
)

PAGE_TOKEN = "<<PDF_PAGE_{page}>>"
PAGE_TOKEN_RE = re.compile(r"<<PDF_PAGE_(\d+)>>")
SOLUTION_RE = re.compile(r"(?im)^SOLUTION(?:\s*\([^)]*\))?:\s*$")
SCORE_RE = re.compile(
    r"(?im)^\s*(\d+(?:\.\d+)?)\s*(?:pt|points?)\.?\s*$"
)


PAPERS: tuple[dict[str, Any], ...] = (
    {
        "paper": "T1",
        "type": "theory",
        "number": 1,
        "title": "A Journey through Time: The Secrets of Avicenna",
        "question_pages": (6, 9),
        "solution_pages": (6, 13),
        "subquestions": 6,
        "raw_total": 25,
        "weight_percent": 7,
        "field": "organic, inorganic, and analytical chemistry",
    },
    {
        "paper": "T2",
        "type": "theory",
        "number": 2,
        "title": "Kinetics of the Belousov-Zhabotinsky Reaction",
        "question_pages": (15, 18),
        "solution_pages": (14, 21),
        "subquestions": 7,
        "raw_total": 35,
        "weight_percent": 6,
        "field": "chemical kinetics and thermodynamics",
    },
    {
        "paper": "T3",
        "type": "theory",
        "number": 3,
        "title": "Into Reticular Chemistry",
        "question_pages": (25, 31),
        "solution_pages": (22, 31),
        "subquestions": 7,
        "raw_total": 63,
        "weight_percent": 7,
        "field": "reticular and materials chemistry",
    },
    {
        "paper": "T4",
        "type": "theory",
        "number": 4,
        "title": "The Nuclear Past of Uzbekistan",
        "question_pages": (37, 39),
        "solution_pages": (32, 37),
        "subquestions": 9,
        "raw_total": 22,
        "overview_total": 24,
        "weight_percent": 6,
        "field": "nuclear chemistry and thermochemistry",
    },
    {
        "paper": "T5",
        "type": "theory",
        "number": 5,
        "title": "Cardiolipins",
        "question_pages": (44, 47),
        "solution_pages": (38, 47),
        "subquestions": 6,
        "raw_total": 18,
        "weight_percent": 6,
        "field": "organic and biological chemistry",
    },
    {
        "paper": "T6",
        "type": "theory",
        "number": 6,
        "title": "Carbon Nanorings",
        "question_pages": (52, 56),
        "solution_pages": (48, 58),
        "subquestions": 7,
        "raw_total": 83,
        "weight_percent": 7,
        "field": "physical organic and nanocarbon chemistry",
    },
    {
        "paper": "T7",
        "type": "theory",
        "number": 7,
        "title": "Nitrogen Fixation",
        "question_pages": (63, 66),
        "solution_pages": (59, 67),
        "subquestions": 7,
        "raw_total": 54,
        "overview_total": 60,
        "weight_percent": 7,
        "field": "inorganic chemistry and industrial catalysis",
    },
    {
        "paper": "T8",
        "type": "theory",
        "number": 8,
        "title": "Recycling of Carbon Dioxide",
        "question_pages": (72, 76),
        "solution_pages": (68, 79),
        "subquestions": 10,
        "raw_total": 84,
        "weight_percent": 7,
        "field": "photochemistry, coordination chemistry, and catalysis",
    },
    {
        "paper": "T9",
        "type": "theory",
        "number": 9,
        "title": "Cyclodextrin Chemistry",
        "question_pages": (84, 88),
        "solution_pages": (80, 90),
        "subquestions": 9,
        "raw_total": 53,
        "weight_percent": 7,
        "field": "organic and supramolecular chemistry",
    },
    {
        "paper": "P1",
        "type": "experiment",
        "number": 1,
        "problem_number": 10,
        "title": "Synthesise and Analyse",
        "question_pages": (10, 15),
        "solution_pages": (10, 20),
        "subquestions": 10,
        "raw_total": 33,
        "weight_percent": 14,
        "field": "inorganic and analytical chemistry",
    },
    {
        "paper": "P2",
        "type": "experiment",
        "number": 2,
        "problem_number": 11,
        "title": "Atlas of Enzymes",
        "question_pages": (19, 25),
        "solution_pages": (24, 34),
        "subquestions": 8,
        "raw_total": 108,
        "weight_percent": 11,
        "field": "biochemistry and analytical chemistry",
    },
    {
        "paper": "P3",
        "type": "experiment",
        "number": 3,
        "problem_number": 12,
        "title": "The Adventures of Hodja Nasreddin",
        "question_pages": (29, 34),
        "solution_pages": (38, 47),
        "subquestions": 9,
        "raw_total": 87,
        "weight_percent": 15,
        "field": "physical and analytical chemistry",
    },
)


# Only genuine backward dependencies are included.  Forward rubric references
# (notably P1.9 mentioning P1.10) are intentionally excluded to avoid cycles.
DEPENDENCIES: dict[str, tuple[str, ...]] = {
    "T1-A6": ("T1-A4", "T1-A5"),
    "T2-A3": ("T2-A2",),
    "T2-A5": ("T2-A2", "T2-A3"),
    "T2-A6": ("T2-A3",),
    "T3-A4": ("T3-A3",),
    "T4-A4": ("T4-A3",),
    "T4-A7": ("T4-A6",),
    "T4-A8": ("T4-A7",),
    "T4-A9": ("T4-A4", "T4-A8"),
    "T5-A2": ("T5-A1",),
    "T5-A3": ("T5-A1", "T5-A2"),
    "T5-A4": ("T5-A3",),
    "T5-A6": ("T5-A2", "T5-A3"),
    "T6-A5": ("T6-A4",),
    "T6-A6": ("T6-A5",),
    "T6-A7": ("T6-A6",),
    "T7-A2": ("T7-A1",),
    "T7-A3": ("T7-A1",),
    "T7-A5": ("T7-A4",),
    "T7-A7": ("T7-A5", "T7-A6"),
    "T8-A2": ("T8-A1",),
    "T8-A4": ("T8-A2",),
    "T8-A6": ("T8-A5",),
    "T8-A7": ("T8-A5", "T8-A6"),
    "T8-A10": ("T8-A9",),
    "T9-A3": ("T9-A2",),
    "T9-A4": ("T9-A3",),
    "T9-A6": ("T9-A5",),
    "T9-A7": ("T9-A5",),
    "T9-A8": ("T9-A5",),
    "P1-A4": ("P1-A3",),
    "P1-A7": ("P1-A5", "P1-A6"),
    "P1-A8": ("P1-A5", "P1-A6"),
    "P1-A9": ("P1-A4", "P1-A8"),
    # P1-A9's rubric reasons forward from the formula requested in A10, so it
    # must not be imported as an A10 prerequisite (that would be circular).
    "P1-A10": ("P1-A8",),
    "P2-A2": ("P2-A1",),
    "P2-A3": ("P2-A1", "P2-A2"),
    "P2-A5": ("P2-A2",),
    "P2-A8": ("P2-A7",),
    "P3-A3": ("P3-A2",),
    "P3-A4": ("P3-A3",),
    "P3-A5": ("P3-A1", "P3-A2"),
    "P3-A7": ("P3-A6",),
    "P3-A9": ("P3-A8",),
}


# Conservative formalization subset: fixed, text-expressible targets only.
THEORY_READY = {
    "T1-A3", "T1-A6",
    "T2-A2", "T2-A3", "T2-A5",
    "T3-A1", "T3-A2", "T3-A6", "T3-A7",
    "T4-A1", "T4-A4", "T4-A5", "T4-A6", "T4-A7", "T4-A8", "T4-A9",
    "T5-A1", "T5-A3", "T5-A4",
    "T6-A3", "T6-A4", "T6-A7",
    "T7-A2", "T7-A3",
    "T8-A5", "T8-A6", "T8-A9",
    "T9-A1", "T9-A3", "T9-A6", "T9-A7", "T9-A9",
}
EXPERIMENT_READY = {"P1-A10", "P2-A4", "P3-A5", "P3-A7"}
FORMALIZATION_READY = THEORY_READY | EXPERIMENT_READY


VISUAL_SOLUTION_IDS = {
    "T3-A3", "T3-A4", "T3-A5",
    "T5-A2", "T5-A6",
    "T6-A2", "T6-A5", "T6-A6",
    "T7-A1", "T7-A5",
    "T8-A2", "T8-A3", "T8-A4", "T8-A7", "T8-A8",
    "T9-A2", "T9-A4", "T9-A5", "T9-A8",
    "P1-A1", "P2-A1", "P2-A2", "P2-A3", "P2-A5", "P2-A6", "P2-A7",
    "P2-A8", "P3-A1", "P3-A3", "P3-A7",
}


# Blank answer-sheet pages contain options, matrices, and drawing templates.
# These are inputs, not solution pages, and therefore do not leak answers.
EXPERIMENT_ANSWER_PAGES: dict[str, dict[int, tuple[int, ...]]] = {
    "P1": {
        **{q: (16,) for q in range(1, 5)},
        **{q: (17,) for q in range(5, 8)},
        **{q: (18,) for q in range(8, 11)},
    },
    "P2": {
        **{q: (26,) for q in range(1, 4)},
        **{q: (27,) for q in range(4, 7)},
        **{q: (28,) for q in range(7, 9)},
    },
    "P3": {
        1: (35,),
        2: (36, 37, 38, 39),
        3: (40, 41),
        4: (41,),
        5: (41,),
        6: (42,),
        7: (42,),
        8: (42,),
        9: (42,),
    },
}
EXPERIMENT_ANSWER_START = {"P1": 16, "P2": 26, "P3": 35}

# Additional non-adjacent question pages needed for visual context.  T5.3
# explicitly allows use of the a-d fragments printed on T5 page 1.
EXTRA_QUESTION_LOCAL_PAGES: dict[str, tuple[int, ...]] = {
    "T5-A3": (1,),
}


# Human transcriptions of answer information embedded as PDF vectors or ticks.
# They are prepended to, not substituted for, extracted official rubric text.
ANSWER_OVERRIDES = {
    "P1-A5": "T1: (d); T2: (d); T3: (b), with (c) also allowed for T3.",
    "P1-A6": "Choose (c) and exactly one of (a) or (b); (d) is incorrect.",
    "P1-A7": "T1 identifies X−; T2 identifies Mᵏ+; T3 and T4 identify X− and Py.",
    "P1-A8": "Intended identification: X− = SCN− and Mᵏ+ = Zn²+; the rubric also accepts alternatives consistent with the student's observations.",
    "P1-A10": "Intended formula: Zn(Py)₂X₂; Zn(Py)₂(SCN)₂ and Zn(Py)₂(NCS)₂ are both accepted.",
    "P2-A1": (
        "Official colour matrix, columns S1–S10: "
        "E1=[N,PR,N,N,PR,N,PR,N,N,PR]; "
        "E2=[G,N,G,N,N,N,G,N,G,N]; "
        "E3=[N,N,N,PR,PR,N,N,PR,PR,N]; "
        "E4=[N,N,PR,PR,N,PR,N,N,N,PR]; "
        "E5=[PR,PR,N,N,N,PR,N,PR,N,N]."
    ),
    "P2-A2": "E1→iv, E2→ii, E3→v, E4→iii, E5→i.",
    "P2-A3": "S6=i+iii; S7=ii+iv; S8=i+v; S9=ii+v; S10=iii+iv.",
    "P2-A4": "The coloured-product reactions are POD and NEZ.",
    "P2-A5": (
        "E1={CHE,CHO,POD}; E2={URE,NEZ}; E3={LIP,POD,GPO,GLK}; "
        "E4={UOX,POD}; E5={GOD,POD}."
    ),
    "P2-A6": "F: M3<M1<M2; G: M2<M3<M1; H: M1<M2<M3.",
    "P2-A7": (
        "Official matrix, columns W1–W7: "
        "E1=[N,N,N,N,PR,N,N]; E2=[Y,G,Y,Y,Y,Y,G]; "
        "E3=[N,N,N,N,PR,N,N]; E4=[N,N,N,N,PR,N,N]; "
        "E5=[N,N,N,N,PR,N,N]."
    ),
    "P2-A8": (
        "W2: 2 phenol + NH₄Cl + 3 HOCl → indophenol dye + 4 HCl + 3 H₂O. "
        "W5: 4-aminoantipyrine + phenol + 4 K₃[Fe(CN)₆] → the shown "
        "quinone-imine dye + 4 K₃H[Fe(CN)₆]. "
        "W7: p-aminophenol + phenol + 2 HOCl → indophenol dye + 2 HCl + 2 H₂O."
    ),
    "P3-A1": "The official checked value is pH = 3.",
    "P3-A4": "X1=HB; X2=HA+H₂C; X3=H₂C; X4=HA+HB; X5=HA; X6=HB+H₂C.",
    "P3-A5": "pH = 3; mixing equal volumes preserves the relevant concentration and acid/conjugate-base ratios.",
    "P3-A6": "Increasing-pH colour order: R < V < B < G < Y.",
    "P3-A7": "Full-credit order: B < A < D < C; B < A < C < D receives partial credit.",
    "P3-A8": "Full-credit ranges allow 4–5 and/or 5–6 for the first transition, and 8–9 and/or 9–10 for the second.",
    "P3-A9": "Intended composition: methyl red (MR) + thymol blue (TB); MR + BTB is conditionally accepted when Q3.8 reports the lower second-transition range.",
}


ANSWER_TYPE_BY_KIND = {
    "theory": "Expression or Numerical Value",
    "structure-drawing": "Chemical Structure or Diagram",
    "chemical-equation": "Chemical or Nuclear Equation",
    "classification": "Multiple Choice, Ordering, or Classification",
    "table-completion": "Table or Classification",
    "physical-product": "Experimental Product",
    "measurement": "Experimental Measurement",
    "experiment-derived": "Expression, Chemical Identity, or Equation",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_pages(path: Path) -> dict[int, str]:
    text = path.read_text(encoding="utf-8")
    markers = list(
        re.finditer(r"^===== PDF PAGE (\d+) =====\n", text, flags=re.MULTILINE)
    )
    if not markers:
        raise ValueError(f"No page markers in {path}")
    pages: dict[int, str] = {}
    for index, marker in enumerate(markers):
        end = markers[index + 1].start() if index + 1 < len(markers) else len(text)
        pages[int(marker.group(1))] = text[marker.end():end].strip()
    return pages


def clean_page(text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped in {"Theory", "Experiment", "English (Official)"}:
            continue
        if re.fullmatch(r"[QGA]\d+-\d+", stripped):
            continue
        lines.append(line.rstrip())
    return "\n".join(lines)


def join_pages(pages: dict[int, str], start: int, end: int) -> str:
    missing = [page for page in range(start, end + 1) if page not in pages]
    if missing:
        raise ValueError(f"Missing extracted PDF pages: {missing}")
    chunks: list[str] = []
    for page in range(start, end + 1):
        chunks.extend([PAGE_TOKEN.format(page=page), clean_page(pages[page])])
    return "\n".join(chunks)


def normalize_text(text: str) -> str:
    text = PAGE_TOKEN_RE.sub(" ", text)
    text = text.replace("\u00ad", "")
    text = re.sub(r"(?<=\w)-\s*\n\s*(?=\w)", "", text)
    return re.sub(r"\s+", " ", text).strip()


def page_before(text: str, position: int) -> int:
    pages = PAGE_TOKEN_RE.findall(text[:position])
    if not pages:
        raise ValueError("Subquestion occurs before any page sentinel")
    return int(pages[-1])


def remove_grading_grid(text: str, spec: dict[str, Any]) -> str:
    """Remove the repeated qid/points grid while preserving all problem text."""
    lines = text.splitlines()
    qids = [f"{spec['number']}.{q}" for q in range(1, spec["subquestions"] + 1)]
    start: int | None = None
    for index in range(0, len(lines) - len(qids) + 1):
        if [line.strip() for line in lines[index:index + len(qids)]] == qids:
            start = index
            break
    if start is None:
        raise ValueError(f"Could not find grading grid for {spec['paper']}")

    search_end = min(len(lines), start + 3 * len(qids) + 12)
    total = str(spec["raw_total"])
    total_indices = [
        index
        for index in range(start + len(qids), search_end)
        if lines[index].strip() in {total, f"{total}.0"}
    ]
    if not total_indices:
        raise ValueError(f"Could not find grading total for {spec['paper']}")
    end = total_indices[-1] + 1
    if start > 0 and lines[start - 1].strip() == "Question":
        start -= 1
    return "\n".join(lines[:start] + lines[end:])


def marker_pattern(spec: dict[str, Any], subquestion: int | None = None) -> re.Pattern[str]:
    prefix = "Q" if spec["type"] == "experiment" else ""
    number = spec["number"]
    suffix = str(subquestion) if subquestion is not None else r"\d+"
    return re.compile(rf"(?m)^{prefix}{number}\.{suffix}\s*$")


def source_part_id(spec: dict[str, Any], subquestion: int) -> str:
    return f"{spec['paper']}-A{subquestion}"


def source_marker(spec: dict[str, Any], subquestion: int) -> str:
    prefix = "Q" if spec["type"] == "experiment" else ""
    return f"{prefix}{spec['number']}.{subquestion}"


def extract_source_parts(
    spec: dict[str, Any], pages: dict[int, str]
) -> list[dict[str, Any]]:
    start_page, end_page = spec["question_pages"]
    group = remove_grading_grid(join_pages(pages, start_page, end_page), spec)
    positions: list[re.Match[str]] = []
    for subquestion in range(1, spec["subquestions"] + 1):
        matches = list(marker_pattern(spec, subquestion).finditer(group))
        if len(matches) != 1:
            raise ValueError(
                f"Expected one problem marker for {spec['paper']} q{subquestion}, "
                f"found {len(matches)}"
            )
        positions.append(matches[0])

    parts: list[dict[str, Any]] = []
    for index, match in enumerate(positions):
        end = positions[index + 1].start() if index + 1 < len(positions) else len(group)
        segment = group[match.end():end]
        score = SCORE_RE.search(segment)
        if score is None:
            raise ValueError(f"No score after {source_marker(spec, index + 1)}")
        current_question = normalize_text(segment[:score.start()])
        if not current_question:
            raise ValueError(f"Empty question for {source_marker(spec, index + 1)}")

        context_raw = group[:match.start()]
        context_raw = SCORE_RE.sub(" ", context_raw)
        context = normalize_text(context_raw)
        trailing_context = normalize_text(segment[score.end():])
        page = page_before(group, match.start())
        parts.append(
            {
                "source_part_id": source_part_id(spec, index + 1),
                "source_label": f"{spec['number']}.{index + 1}",
                "subquestion": index + 1,
                "current_question": current_question,
                "context": context,
                "trailing_context": trailing_context,
                "points": float(score.group(1)),
                "source_page": page,
                "printed_page": page - start_page + 1,
            }
        )
    return parts


def extract_solution_parts(
    spec: dict[str, Any],
    pages: dict[int, str],
    source_parts: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    start_page, end_page = spec["solution_pages"]
    group = remove_grading_grid(join_pages(pages, start_page, end_page), spec)

    all_qid_matches: list[tuple[int, str, re.Match[str]]] = []
    for subquestion in range(1, spec["subquestions"] + 1):
        for match in marker_pattern(spec, subquestion).finditer(group):
            all_qid_matches.append((subquestion, source_marker(spec, subquestion), match))
    all_qid_matches.sort(key=lambda item: item[2].start())

    first_solution_by_q: dict[int, tuple[re.Match[str], re.Match[str]]] = {}
    for solution_match in SOLUTION_RE.finditer(group):
        preceding = [item for item in all_qid_matches if item[2].start() < solution_match.start()]
        if not preceding:
            continue
        subquestion, _label, qid_match = preceding[-1]
        first_solution_by_q.setdefault(subquestion, (qid_match, solution_match))

    starts: list[re.Match[str]] = []
    solution_markers: list[re.Match[str] | None] = []
    for subquestion, source_part in enumerate(source_parts, start=1):
        if subquestion in first_solution_by_q:
            qid_match, solution_match = first_solution_by_q[subquestion]
        elif source_part["points"] == 0:
            matches = list(marker_pattern(spec, subquestion).finditer(group))
            if len(matches) != 1:
                raise ValueError(
                    f"No unique zero-point marker for {spec['paper']} q{subquestion}"
                )
            qid_match, solution_match = matches[0], None
        else:
            raise ValueError(f"No solution marker for {spec['paper']} q{subquestion}")
        starts.append(qid_match)
        solution_markers.append(solution_match)

    if any(a.start() >= b.start() for a, b in zip(starts, starts[1:])):
        raise ValueError(f"Non-monotonic solution starts for {spec['paper']}")

    results: list[dict[str, Any]] = []
    for index, (qid_match, solution_match) in enumerate(zip(starts, solution_markers)):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(group)
        segment = group[qid_match.end():end]
        source_part = source_parts[index]

        if solution_match is None:
            answer = "Experimental data table; this item is not graded in the official rubric."
            solution_prompt = normalize_text(segment[:SCORE_RE.search(segment).start()])
        else:
            local_solution_start = solution_match.start() - qid_match.end()
            local_solution_end = solution_match.end() - qid_match.end()
            solution_prompt = normalize_text(segment[:local_solution_start])
            answer = normalize_text(segment[local_solution_end:])
            trailing = source_part["trailing_context"]
            if trailing:
                if not answer.endswith(trailing):
                    raise ValueError(
                        f"Solution/context boundary mismatch for {spec['paper']} "
                        f"q{index + 1}"
                    )
                answer = answer[:-len(trailing)].rstrip()
            answer = re.sub(r"(?i)\s*SOLUTION:\s*$", "", answer).rstrip()

        if solution_prompt != source_part["current_question"]:
            raise ValueError(
                f"Problem/solution prompt mismatch for {spec['paper']} q{index + 1}:\n"
                f"problem={source_part['current_question']!r}\n"
                f"solution={solution_prompt!r}"
            )

        part_id = source_part["source_part_id"]
        if part_id in ANSWER_OVERRIDES:
            answer = (
                "Curated transcription of the graphical official answer: "
                f"{ANSWER_OVERRIDES[part_id]}\n\n"
                f"Extracted official solution and rubric: {answer}"
            )
        if part_id in VISUAL_SOLUTION_IDS:
            answer = (
                "Visual-answer notice: the official solution contains essential "
                "ticks, structures, tables, graphs, or equations that PDF plain-text "
                "extraction may omit. Consult the cited solution PDF page.\n\n"
                f"{answer}"
            )
        if not answer:
            answer = "See the cited official solution PDF page; no plain text was extractable."

        results.append(
            {
                "answer": answer,
                "solution_page": page_before(group, qid_match.start()),
            }
        )
    return results


def classify_kind(spec: dict[str, Any], part_id: str, question: str) -> str:
    lower = question.lower()
    if spec["type"] == "experiment":
        if part_id == "P1-A1":
            return "physical-product"
        if any(token in lower for token in ("record your", "observed", "performed reactions", "titration")):
            return "measurement"
        if any(token in lower for token in ("calculate", "determine", "write", "give the ph")):
            return "experiment-derived"
        return "classification"
    if "draw" in lower or "structure" in lower and "tick" not in lower:
        return "structure-drawing"
    if "write" in lower and "equation" in lower:
        return "chemical-equation"
    if re.search(r"\b(?:tick|choose|rank|arrange)\b", lower):
        return "classification"
    if "fill" in lower and "table" in lower:
        return "table-completion"
    return "theory"


def raw_files_for(spec: dict[str, Any]) -> tuple[str, str, str, str]:
    prefix = "theory" if spec["type"] == "theory" else "experiment"
    return (
        f"{prefix}_problem.pdf",
        f"{prefix}_solution.pdf",
        f"{prefix}_problem.txt",
        f"{prefix}_solution.txt",
    )


def image_names_for(spec: dict[str, Any], part: dict[str, Any]) -> list[str]:
    question_start, _question_end = spec["question_pages"]
    local_page = part["source_page"] - question_start + 1
    names = [f"{spec['paper']}_page-{local_page}.png"]

    # The immediately preceding question page is useful for setups crossing a page.
    if local_page > 1:
        names.append(f"{spec['paper']}_page-{local_page - 1}.png")

    # For the first experimental subquestion, retain all equipment/setup pages.
    if spec["type"] == "experiment" and part["subquestion"] == 1:
        for earlier in range(local_page - 2, 0, -1):
            names.append(f"{spec['paper']}_page-{earlier}.png")

    for extra_page in EXTRA_QUESTION_LOCAL_PAGES.get(part["source_part_id"], ()):
        names.append(f"{spec['paper']}_page-{extra_page}.png")

    for answer_page in EXPERIMENT_ANSWER_PAGES.get(spec["paper"], {}).get(
        part["subquestion"], ()
    ):
        local_answer_page = answer_page - EXPERIMENT_ANSWER_START[spec["paper"]] + 1
        names.append(f"{spec['paper']}_answer_page-{local_answer_page}.png")

    return list(dict.fromkeys(names))


def close_dependency_source_images(parts: list[dict[str, Any]]) -> None:
    """Add the source pages needed to reconstruct every prior-part dependency.

    A target already carries its current page and the immediately preceding
    setup page.  A dependency contributes its own current page plus any
    explicitly curated non-adjacent problem pages.  The contribution is
    transitive, deterministic, and keeps the target's primary
    page first.  This is intentionally metadata-driven: it neither scans the
    PDF nor guesses pages from problem prose.
    """

    by_part: dict[str, dict[str, Any]] = {}
    for part in parts:
        part_id = str(part.get("source_part_id") or "")
        if not part_id or part_id in by_part:
            raise ValueError(f"Invalid or duplicate source_part_id: {part_id!r}")
        by_part[part_id] = part

    spec_by_paper = {str(spec["paper"]): spec for spec in PAPERS}
    visiting: set[str] = set()
    cache: dict[str, tuple[str, ...]] = {}

    def dependency_evidence(part_id: str) -> tuple[str, ...]:
        cached = cache.get(part_id)
        if cached is not None:
            return cached
        if part_id in visiting:
            raise ValueError(f"Cyclic source dependency at {part_id}")
        part = by_part.get(part_id)
        if part is None:
            raise ValueError(f"Missing source dependency: {part_id}")
        paper = str(part.get("paper") or "")
        spec = spec_by_paper.get(paper)
        if spec is None:
            raise ValueError(f"Unknown paper for {part_id}: {paper!r}")

        question_start, _question_end = spec["question_pages"]
        local_page = int(part["source_page"]) - int(question_start) + 1
        names = [f"{paper}_page-{local_page}.png"]
        names.extend(
            f"{paper}_page-{extra_page}.png"
            for extra_page in EXTRA_QUESTION_LOCAL_PAGES.get(part_id, ())
        )
        visiting.add(part_id)
        for dependency_id in part.get("dependencies", ()):
            if dependency_id not in by_part:
                raise ValueError(f"{part_id} references missing {dependency_id}")
            names.extend(dependency_evidence(str(dependency_id)))
        visiting.remove(part_id)
        result = tuple(dict.fromkeys(names))
        cache[part_id] = result
        return result

    for part in parts:
        images = list(part["images"])
        for dependency_id in part.get("dependencies", ()):
            images.extend(dependency_evidence(str(dependency_id)))
        part["images"] = list(dict.fromkeys(images))


def build_parts() -> list[dict[str, Any]]:
    theory_problem_pages = read_pages(TEXT / "theory_problem.txt")
    theory_solution_pages = read_pages(TEXT / "theory_solution.txt")
    experiment_problem_pages = read_pages(TEXT / "experiment_problem.txt")
    experiment_solution_pages = read_pages(TEXT / "experiment_solution.txt")

    parts: list[dict[str, Any]] = []
    for spec in PAPERS:
        problem_pages = (
            theory_problem_pages if spec["type"] == "theory" else experiment_problem_pages
        )
        solution_pages = (
            theory_solution_pages if spec["type"] == "theory" else experiment_solution_pages
        )
        source_parts = extract_source_parts(spec, problem_pages)
        solution_parts = extract_solution_parts(spec, solution_pages, source_parts)
        if len(source_parts) != spec["subquestions"]:
            raise ValueError(f"Wrong subquestion count for {spec['paper']}")
        if sum(part["points"] for part in source_parts) != spec["raw_total"]:
            raise ValueError(
                f"Point total mismatch for {spec['paper']}: "
                f"{sum(part['points'] for part in source_parts)} != {spec['raw_total']}"
            )

        for source_part, solution_part in zip(source_parts, solution_parts, strict=True):
            part_id = source_part["source_part_id"]
            part = {
                **source_part,
                **solution_part,
                "paper": spec["paper"],
                "paper_type": spec["type"],
                "title": spec["title"],
                "problem_number": spec.get("problem_number", spec["number"]),
                "field": spec["field"],
                "kind": classify_kind(spec, part_id, source_part["current_question"]),
                "formalization_ready": part_id in FORMALIZATION_READY,
                "dependencies": DEPENDENCIES.get(part_id, ()),
            }
            part["images"] = image_names_for(spec, part)
            parts.append(part)

    if len(parts) != 95:
        raise ValueError(f"Expected 95 IChO subquestions, found {len(parts)}")
    close_dependency_source_images(parts)
    return parts


def build_native_rows(parts: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_part = {part["source_part_id"]: part for part in parts}
    if len(by_part) != len(parts):
        raise ValueError("Duplicate source_part_id")

    rows: list[dict[str, Any]] = []
    for part in parts:
        paper = part["paper"]
        problem_pdf, solution_pdf, _problem_text, _solution_text = raw_files_for(
            next(spec for spec in PAPERS if spec["paper"] == paper)
        )
        required = [RAW / problem_pdf, RAW / solution_pdf]
        required.extend(IMAGE / name for name in part["images"])
        missing = [str(path) for path in required if not path.is_file()]
        if missing:
            raise FileNotFoundError("Missing IChO source assets: " + ", ".join(missing))

        dependencies = []
        for dependency_id in part["dependencies"]:
            if dependency_id not in by_part:
                raise ValueError(f"{part['source_part_id']} references {dependency_id}")
            dependency = by_part[dependency_id]
            dependencies.append(
                {
                    "source_id": f"icho_2026_{dependency_id.lower().replace('-', '_')}",
                    "part_id": dependency_id,
                    "question": dependency["current_question"],
                    "answer": dependency["answer"],
                    "reusable_conclusions": [dependency["answer"]],
                    "dependency_policy": (
                        "natural_language_prerequisite_only; the current target "
                        "and later answers must not be assumed"
                    ),
                }
            )

        index = f"icho_2026_{part['source_part_id'].lower().replace('-', '_')}"
        question = "\n".join(
            [
                "## Source",
                "58th International Chemistry Olympiad, Tashkent, Uzbekistan, 2026.",
                f"Official-materials index: {OFFICIAL_MATERIALS_URL}",
                f"English problem PDF: ../icho_2026_source/raw/{problem_pdf}",
                f"English solution/rubric PDF: ../icho_2026_source/raw/{solution_pdf}",
                (
                    f"Problem PDF page {part['source_page']}; printed local question "
                    f"page {part['printed_page']}; solution starts on PDF page "
                    f"{part['solution_page']}."
                ),
                "The page PNG is primary visual evidence for formulas, structures, tables, and figures.",
                "",
                f"## {paper}. {part['title']}",
                part["context"],
                "",
                f"## Current subquestion {part['source_label']}",
                part["current_question"],
                "",
                "## Dataset metadata",
                (
                    f"IChO 2026; {paper}; raw rubric points={part['points']:g}; "
                    f"kind={part['kind']}; "
                    f"formalization_ready={str(part['formalization_ready']).lower()}."
                ),
            ]
        ).strip()

        row = {
            "id": index,
            "index": index,
            "source_index": part["source_part_id"],
            "problem_id": f"icho_2026_{paper.lower()}",
            "part_id": part["source_part_id"],
            "question": question,
            "current_question": part["current_question"],
            "shared_context": part["context"],
            "answer": part["answer"],
            "category": (
                "IChO 2026 Theory" if part["paper_type"] == "theory" else "IChO 2026 Experiment"
            ),
            "dataset": "IChO 2026 official English exam materials",
            "dataset_format": "native",
            "points": part["points"],
            "paper": paper,
            "kind": part["kind"],
            "formalization_ready": part["formalization_ready"],
            "image": part["images"][0],
            "images": part["images"],
            "previous_parts": dependencies,
            "source_pdf": problem_pdf,
            "source_page": part["source_page"],
            "printed_page": part["printed_page"],
            "solution_pdf": solution_pdf,
            "marking_scheme_pdf": solution_pdf,
            "source_url": SOURCE_URLS[problem_pdf],
            "solution_url": SOURCE_URLS[solution_pdf],
        }
        if tuple(row) != NATIVE_SCHEMA_FIELDS:
            raise ValueError(f"Native field order/set mismatch for {index}")
        rows.append(row)
    return rows


def canonical_identity(part: dict[str, Any]) -> dict[str, Any]:
    problem_number = int(part["problem_number"])
    subquestion = int(part["subquestion"])
    problem_id = f"IChO_2026_{problem_number}"
    return {
        "index": f"{problem_id}_A_{subquestion}",
        "problem_id": problem_id,
        "problem_number": problem_number,
        "part_id": f"A.{subquestion}",
        "part_letter": "A",
        "subquestion_number": subquestion,
    }


def build_archon_rows(
    parts: list[dict[str, Any]], native_rows: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    if len(parts) != len(native_rows):
        raise ValueError("Parts/native rows are not aligned")
    part_by_id = {part["source_part_id"]: part for part in parts}
    identity_by_id = {
        source_id: canonical_identity(part) for source_id, part in part_by_id.items()
    }

    rows: list[dict[str, Any]] = []
    for part, native in zip(parts, native_rows, strict=True):
        source_id = part["source_part_id"]
        identity = identity_by_id[source_id]
        image_entries = []
        for position, name in enumerate(native["images"]):
            is_answer_sheet = "_answer_page-" in name
            image_entries.append(
                {
                    "path": name,
                    "original_path": f"image/{name}",
                    "role": (
                        "official_blank_answer_sheet" if is_answer_sheet else "official_source_page"
                    ),
                    "evidence": (
                        "Rendered from the official blank English answer sheet; it contains "
                        "the response layout or options but no solution."
                        if is_answer_sheet
                        else (
                            "Rendered from the official IChO 2026 English problem PDF; "
                            + (
                                "this is the primary page for the current subquestion."
                                if position == 0
                                else "this is a preceding context/setup page."
                            )
                        )
                    ),
                }
            )

        previous_parts = []
        for dependency_id in part["dependencies"]:
            dependency = part_by_id[dependency_id]
            dependency_identity = identity_by_id[dependency_id]
            previous_parts.append(
                {
                    "source_id": dependency_identity["index"],
                    "part_id": dependency_identity["part_id"],
                    "question": dependency["current_question"],
                    "answer": dependency["answer"],
                    "reusable_conclusions": [dependency["answer"]],
                    "dependency_policy": (
                        "natural_language_prerequisite_only; do_not_import_Lean_output"
                    ),
                }
            )

        context = native["shared_context"].strip()
        current_question = native["current_question"].strip()
        question = f"{context}\n\nCurrent subquestion:\n{current_question}"
        answer = native["answer"].strip()
        solution_page = part["solution_page"]

        row = {
            "index": identity["index"],
            "category": "chemistry",
            "source_dataset": "IChO 2026 official English exam materials",
            "source_dataset_url": OFFICIAL_MATERIALS_URL,
            "year": 2026,
            "problem_id": identity["problem_id"],
            "problem_number": identity["problem_number"],
            "part_id": identity["part_id"],
            "part_letter": identity["part_letter"],
            "subquestion_number": identity["subquestion_number"],
            "formalization_input_policy": {
                "previous_parts": (
                    "Natural-language prerequisites only; do not import or depend on "
                    "previous Lean outputs."
                ),
                "images": (
                    "Use only listed official problem pages and blank answer sheets. "
                    "Never infer an answer from an unlisted solution page."
                ),
            },
            "context": context,
            "current_question": current_question,
            "question": question,
            "answer": answer,
            "answers": [answer],
            "marking": [[
                f"Official solution and rubric: raw/{native['solution_pdf']}, "
                f"starting at PDF page {solution_page}; this subquestion is worth "
                f"{part['points']:g} raw rubric points."
            ]],
            "answer_type": [ANSWER_TYPE_BY_KIND[part["kind"]]],
            "unit": [None],
            "points": [part["points"]],
            "modality": "text+official source-page image",
            "field": part["field"],
            "source": f"IChO_2026_{part['paper']}",
            "previous_parts": previous_parts,
            "previous_part_count": len(previous_parts),
            "images": image_entries,
            "image": native["image"],
            "image_count": len(image_entries),
            "raw_hipho_image_question": [],
        }
        if tuple(row) != ARCHON_SCHEMA_FIELDS:
            raise ValueError(f"Archon field order/set mismatch for {identity['index']}")
        rows.append(row)

    validate_archon_rows(rows)
    return rows


def validate_archon_rows(rows: list[dict[str, Any]]) -> None:
    expected_fields = set(ARCHON_SCHEMA_FIELDS)
    if HIPHO_REFERENCE.is_file():
        with HIPHO_REFERENCE.open("r", encoding="utf-8") as handle:
            reference = json.loads(next(line for line in handle if line.strip()))
        if set(reference) != expected_fields:
            raise ValueError("Static 29-field schema differs from HiPhO reference")

    seen: set[str] = set()
    for number, row in enumerate(rows, start=1):
        if set(row) != expected_fields:
            raise ValueError(f"Archon row {number} has incompatible fields")
        index = row["index"]
        if index in seen:
            raise ValueError(f"Duplicate Archon index: {index}")
        seen.add(index)
        if row["answer"] != row["answers"][0]:
            raise ValueError(f"answer/answers mismatch for {index}")
        aligned = [row["answers"], row["answer_type"], row["unit"], row["points"]]
        if len({len(values) for values in aligned}) != 1:
            raise ValueError(f"Answer metadata arrays are not aligned for {index}")
        if row["previous_part_count"] != len(row["previous_parts"]):
            raise ValueError(f"Bad previous_part_count for {index}")
        if row["image_count"] != len(row["images"]):
            raise ValueError(f"Bad image_count for {index}")
        if not row["images"] or row["image"] != row["images"][0]["path"]:
            raise ValueError(f"Primary image mismatch for {index}")
        for image in row["images"]:
            if not (IMAGE / image["path"]).is_file():
                raise FileNotFoundError(IMAGE / image["path"])


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows),
        encoding="utf-8",
    )


def write_review(
    parts: list[dict[str, Any]],
    native_rows: list[dict[str, Any]],
    archon_rows: list[dict[str, Any]],
) -> None:
    REVIEW.mkdir(parents=True, exist_ok=True)
    columns = (
        "index", "source", "kind", "formalization_ready", "points",
        "source_page", "solution_page", "image_count", "previous_part_count",
        "current_question", "answer",
    )
    preview_lines = ["\t".join(columns)]
    for part, native, archon in zip(parts, native_rows, archon_rows, strict=True):
        values: dict[str, Any] = {
            **archon,
            "source_page": native["source_page"],
            "solution_page": part["solution_page"],
            "kind": native["kind"],
            "formalization_ready": native["formalization_ready"],
            "points": native["points"],
        }
        preview_lines.append(
            "\t".join(
                " ".join(str(values[column]).replace("\t", " ").split())
                for column in columns
            )
        )
    (REVIEW / "preview.tsv").write_text(
        "\n".join(preview_lines) + "\n", encoding="utf-8"
    )

    sample_indices = (0, 5, 21, 44, 67, 68, 77, 94)
    (REVIEW / "sample_items.json").write_text(
        json.dumps([archon_rows[index] for index in sample_indices], ensure_ascii=False, indent=2)
        + "\n",
        encoding="utf-8",
    )

    unique_images = sorted({image["path"] for row in archon_rows for image in row["images"]})
    by_problem = Counter(row["source"] for row in archon_rows)
    summary = "\n".join(
        [
            "# IChO 2026 Archon Input Review",
            "",
            f"- Items: {len(archon_rows)} (68 theory + 27 experiment)",
            f"- By paper: {dict(by_problem)}",
            f"- Formalization-ready subset: {sum(row['formalization_ready'] for row in native_rows)}",
            f"- Items with explicit previous-part dependencies: {sum(row['previous_part_count'] > 0 for row in archon_rows)}",
            f"- Unique rendered input pages: {len(unique_images)}",
            "",
            "## Compatibility",
            "",
            "- Every Archon row has exactly the same 29 top-level fields as `hipho_ipho_2024_2025_archon.jsonl`.",
            "- Theory papers map to problem numbers 1–9; practical papers P1–P3 map to 10–12.",
            "- `previous_parts` are explicit natural-language prerequisites and never import Lean output.",
            "- The first image is always the current official question page; blank answer sheets never contain solutions.",
            "",
            "## Source caveats",
            "",
            "- Raw per-subquestion rubric points are stored. Competition percentages remain in `processed/manifest.json`.",
            "- The official overview says T4=24 and T7=60 raw points, while each paper's own grid and per-item rubrics sum to T4=22 and T7=54. This dataset follows the per-item rubrics.",
            "- PDF plain text omits some vector structures, ticks, and tables. Affected answers are flagged and retain exact solution-page provenance; selected experimental visuals were manually transcribed.",
            "- P3.3 has no universal numeric official answer: the official rubric uses local master-value placeholders. No value was invented.",
            "",
            "## Primary inputs",
            "",
            "- `icho_2026_source/icho_2026_archon.jsonl`",
            "- `icho_2026_source/icho_2026_archon_pipeline.jsonl`",
            "",
        ]
    )
    (REVIEW / "summary.md").write_text(summary, encoding="utf-8")

    review_manifest = {
        "source_dataset": "IChO 2026 official English exam materials",
        "source_dataset_url": OFFICIAL_MATERIALS_URL,
        "generated_items": len(archon_rows),
        "schema_reference": "hipho_ipho_2024_2025/hipho_ipho_2024_2025_archon.jsonl",
        "schema_field_count": len(ARCHON_SCHEMA_FIELDS),
        "schema_fields": list(ARCHON_SCHEMA_FIELDS),
        "output_jsonl": "icho_2026_source/icho_2026_archon.jsonl",
        "image_files": len(unique_images),
        "notes": [
            "All inputs are official problem pages or blank answer sheets; solution pages are provenance only.",
            "raw_hipho_image_question is empty because IChO is not a SciYu/HiPhO source.",
            "Graphical-answer notices identify rows whose extracted solution text is incomplete.",
        ],
    }
    (REVIEW / "manifest.json").write_text(
        json.dumps(review_manifest, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def main() -> None:
    PROCESSED.mkdir(parents=True, exist_ok=True)
    REVIEW.mkdir(parents=True, exist_ok=True)

    parts = build_parts()
    native_rows = build_native_rows(parts)
    archon_rows = build_archon_rows(parts, native_rows)
    theory_rows = [row for row in native_rows if row["paper"].startswith("T")]
    experiment_rows = [row for row in native_rows if row["paper"].startswith("P")]
    pipeline_rows = [row for row in native_rows if row["formalization_ready"]]
    archon_pipeline_rows = [
        archon
        for archon, native in zip(archon_rows, native_rows, strict=True)
        if native["formalization_ready"]
    ]

    native_outputs = {
        "icho_2026_all.jsonl": native_rows,
        "icho_2026_theory.jsonl": theory_rows,
        "icho_2026_experiment.jsonl": experiment_rows,
        "icho_2026_pipeline.jsonl": pipeline_rows,
    }
    for name, rows in native_outputs.items():
        write_jsonl(PROCESSED / name, rows)

    archon_outputs = {
        "icho_2026_archon.jsonl": archon_rows,
        "icho_2026_archon_pipeline.jsonl": archon_pipeline_rows,
    }
    for name, rows in archon_outputs.items():
        write_jsonl(SOURCE / name, rows)

    (PROCESSED / "icho_2026_entries.json").write_text(
        json.dumps(native_rows, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    write_review(parts, native_rows, archon_rows)

    source_files = []
    for name, url in SOURCE_URLS.items():
        path = RAW / name
        if not path.is_file():
            raise FileNotFoundError(path)
        source_files.append(
            {
                "file": f"raw/{name}",
                "url": url,
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            }
        )

    paper_counts = Counter(row["paper"] for row in native_rows)
    kind_counts = Counter(row["kind"] for row in native_rows)
    paper_metadata = {
        spec["paper"]: {
            "title": spec["title"],
            "items": spec["subquestions"],
            "raw_rubric_points": spec["raw_total"],
            "problem_weight_percent": spec["weight_percent"],
            **(
                {"overview_reported_raw_points": spec["overview_total"]}
                if "overview_total" in spec else {}
            ),
        }
        for spec in PAPERS
    }
    manifest = {
        "schema_version": 2,
        "competition": "58th International Chemistry Olympiad",
        "year": 2026,
        "location": "Tashkent, Uzbekistan",
        "language": "English (Official)",
        "source_status": (
            "Official exam materials are public on the organizer's materials page. "
            "The checked-in combined English PDFs are verified copies from the Dutch "
            "Chemistry Olympiad mirror."
        ),
        "official_materials_url": OFFICIAL_MATERIALS_URL,
        "mirror_index_url": MIRROR_INDEX_URL,
        "counts": {
            "all": len(native_rows),
            "theory": len(theory_rows),
            "experiment": len(experiment_rows),
            "formalization_ready": len(pipeline_rows),
            "by_paper": dict(paper_counts),
            "by_kind": dict(kind_counts),
        },
        "paper_metadata": paper_metadata,
        "known_source_inconsistencies": [
            (
                "The official overview table reports T4=24 raw points, but the T4 "
                "paper grid and nine per-item rubrics sum to 22; 22 is stored."
            ),
            (
                "The official overview table reports T7=60 raw points, but the T7 "
                "paper grid and seven per-item rubrics sum to 54; 54 is stored."
            ),
        ],
        "datasets": {
            **{
                f"processed/{name}": {
                    "rows": len(rows),
                    "sha256": sha256(PROCESSED / name),
                    "schema": "provenance-rich",
                }
                for name, rows in native_outputs.items()
            },
            **{
                name: {
                    "rows": len(rows),
                    "sha256": sha256(SOURCE / name),
                    "schema": "hipho-2024-2025-compatible",
                }
                for name, rows in archon_outputs.items()
            },
        },
        "archon_schema_reference": "hipho_ipho_2024_2025/hipho_ipho_2024_2025_archon.jsonl",
        "archon_schema_field_count": len(ARCHON_SCHEMA_FIELDS),
        "source_files": source_files,
    }
    (PROCESSED / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    print(json.dumps(manifest["counts"], ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
