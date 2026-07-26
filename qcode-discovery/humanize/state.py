"""Durable state, candidate archive, and BitLesson memory for qcode RLCR."""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


SCHEMA_VERSION = 1


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + f".tmp-{os.getpid()}")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)


def append_jsonl(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(value, ensure_ascii=False, default=str) + "\n")


def _terms(row: dict[str, Any], name: str) -> list[list[int]]:
    return sorted([list(map(int, term)) for term in row.get(name, [])])


def code_key(row: dict[str, Any]) -> str:
    """Stable content key for a CSS BB code, independent of score metadata."""
    defining = {
        "ell": int(row.get("ell", 0) or 0),
        "m": int(row.get("m", 0) or 0),
        "A_terms": _terms(row, "A_terms"),
        "B_terms": _terms(row, "B_terms"),
    }
    payload = json.dumps(defining, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()[:20]


def candidate_fom(row: dict[str, Any]) -> float:
    value = row.get("fom", row.get("score", 0.0))
    try:
        return float(value or 0.0)
    except (TypeError, ValueError):
        return 0.0


def credible_bp_candidate(row: dict[str, Any], trust_ratio: float = 1.3) -> bool:
    """Apply the same conservative BP-OSD credibility gate as the evaluator."""
    try:
        n = int(row.get("n", 0) or 0)
        k = int(row.get("k", 0) or 0)
        d = int(row.get("d", 0) or 0)
    except (TypeError, ValueError):
        return False
    return n > 0 and k > 0 and d > 0 and d <= trust_ratio * math.sqrt(n)


def archive_cell(row: dict[str, Any]) -> str:
    """Candidate-level MAP-Elites cell used across OpenEvolve rounds."""
    n = int(row.get("n", 0) or 0)
    k = int(row.get("k", 0) or 0)
    rate_bin = int(20 * k / n) if n else 0
    pattern = str(row.get("pattern_type", "unknown"))
    term_count = int(row.get("term_count", 0) or 0)
    if not term_count:
        term_count = len(row.get("A_terms", [])) + len(row.get("B_terms", []))
    return f"n={n}|rate={rate_bin}|pattern={pattern}|terms={term_count}"


class EliteArchive:
    """Persistent best-per-cell archive, complementary to OpenEvolve's archive."""

    def __init__(self, path: Path):
        self.path = path
        self.cells: dict[str, dict[str, Any]] = {}
        if path.is_file():
            raw = json.loads(path.read_text())
            self.cells = dict(raw.get("cells", {}))

    def update(self, rows: Iterable[dict[str, Any]], round_number: int) -> list[dict[str, Any]]:
        promoted: list[dict[str, Any]] = []
        for original in rows:
            row = dict(original)
            row["candidate_key"] = code_key(row)
            row["archive_cell"] = archive_cell(row)
            row["archive_round"] = round_number
            current = self.cells.get(row["archive_cell"])
            if current is None or candidate_fom(row) > candidate_fom(current):
                self.cells[row["archive_cell"]] = row
                promoted.append(row)
        self.save()
        return promoted

    def replace(self, rows: Iterable[dict[str, Any]]) -> None:
        """Rebuild the archive from already-screened rows.

        This is used to purge legacy disconnected/known entries from a failed
        pre-gate run before any resumed MILP audit is scheduled.
        """
        cells: dict[str, dict[str, Any]] = {}
        for original in rows:
            row = dict(original)
            row["candidate_key"] = code_key(row)
            row["archive_cell"] = archive_cell(row)
            current = cells.get(row["archive_cell"])
            if current is None or candidate_fom(row) > candidate_fom(current):
                cells[row["archive_cell"]] = row
        self.cells = cells
        self.save()

    def ranked(self) -> list[dict[str, Any]]:
        return sorted(self.cells.values(), key=candidate_fom, reverse=True)

    def save(self) -> None:
        _atomic_json(self.path, {
            "schema_version": SCHEMA_VERSION,
            "updated_at": utc_now(),
            "cells": self.cells,
        })


@dataclass
class RunStore:
    """Filesystem contract for a resumable Humanize qcode run."""

    root: Path
    run_id: str

    @classmethod
    def create(cls, results_dir: Path, run_id: str) -> "RunStore":
        safe_id = re.sub(r"[^A-Za-z0-9_.-]+", "-", run_id).strip("-")
        if not safe_id:
            raise ValueError("run_id must contain at least one safe character")
        store = cls(results_dir / "humanize" / safe_id, safe_id)
        store.root.mkdir(parents=True, exist_ok=True)
        return store

    @property
    def state_path(self) -> Path:
        return self.root / "state.json"

    @property
    def events_path(self) -> Path:
        return self.root / "events.jsonl"

    @property
    def archive_path(self) -> Path:
        return self.root / "elite-archive.json"

    @property
    def memory_path(self) -> Path:
        return self.root / "bitlesson.md"

    def round_dir(self, number: int) -> Path:
        path = self.root / "rounds" / f"round-{number:03d}"
        path.mkdir(parents=True, exist_ok=True)
        return path

    def load_state(self) -> dict[str, Any] | None:
        if not self.state_path.is_file():
            return None
        state = json.loads(self.state_path.read_text())
        if state.get("schema_version") != SCHEMA_VERSION:
            raise ValueError(
                f"Unsupported Humanize state schema: {state.get('schema_version')}"
            )
        return state

    def initialize(self, config: dict[str, Any]) -> dict[str, Any]:
        existing = self.load_state()
        if existing is not None:
            return existing
        state = {
            "schema_version": SCHEMA_VERSION,
            "run_id": self.run_id,
            "status": "running",
            "created_at": utc_now(),
            "updated_at": utc_now(),
            "current_round": 0,
            "candidate_offset": 0,
            "best_fom": 0.0,
            "no_improvement_rounds": 0,
            "last_checkpoint": None,
            "audited_keys": [],
            "audited_structural_digests": [],
            "config": config,
            "rounds": [],
        }
        self.write_state(state)
        if not self.memory_path.exists():
            self.memory_path.write_text(
                "# Qcode BitLesson memory\n\n"
                "Only evidence-backed lessons from completed independent reviews belong here.\n"
            )
        self.event("run_initialized", config=config)
        return state

    def write_state(self, state: dict[str, Any]) -> None:
        state["updated_at"] = utc_now()
        _atomic_json(self.state_path, state)

    def event(self, event: str, **payload: Any) -> None:
        append_jsonl(self.events_path, {
            "timestamp": utc_now(), "event": event, **payload,
        })

    def add_lessons(self, lessons: Iterable[dict[str, Any]], round_number: int) -> list[str]:
        added: list[str] = []
        known = self.memory_path.read_text() if self.memory_path.exists() else ""
        with self.memory_path.open("a", encoding="utf-8") as stream:
            for lesson in lessons:
                insight = str(lesson.get("insight", "")).strip()
                evidence = str(lesson.get("evidence", "")).strip()
                action = str(lesson.get("action", "")).strip()
                if not insight or not evidence or not action:
                    continue
                digest = hashlib.sha256(
                    f"{insight}\0{evidence}\0{action}".encode()
                ).hexdigest()[:8]
                lesson_id = f"BL-{datetime.now(timezone.utc):%Y%m%d}-{digest}"
                if lesson_id in known:
                    continue
                stream.write(
                    f"\n## {lesson_id}\n"
                    f"- Round: {round_number}\n"
                    f"- Insight: {insight}\n"
                    f"- Evidence: {evidence}\n"
                    f"- Action: {action}\n"
                )
                added.append(lesson_id)
                known += lesson_id
        if added:
            self.event("bitlesson_updated", round_number=round_number, lesson_ids=added)
        return added


def read_jsonl_since(path: Path, offset: int) -> tuple[list[dict[str, Any]], int]:
    """Read complete JSONL records from a byte offset and return the new offset."""
    if not path.is_file():
        return [], offset
    rows: list[dict[str, Any]] = []
    with path.open("rb") as stream:
        size = path.stat().st_size
        if offset < 0 or offset > size:
            offset = 0
        stream.seek(offset)
        for raw in stream:
            try:
                rows.append(json.loads(raw.decode("utf-8")))
            except (UnicodeDecodeError, json.JSONDecodeError):
                continue
        return rows, stream.tell()
