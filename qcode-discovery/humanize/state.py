"""Durable state, candidate archive, and BitLesson memory for qcode RLCR."""

from __future__ import annotations

import hashlib
import json
import os
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from math import gcd
from numbers import Integral
from pathlib import Path
from typing import Any, Iterable, Mapping

from evaluation.geometry import normalize_geometry
from evaluation.structural_features import (
    PATTERN_CLASSIFIER_VERSION,
    classify_pattern,
    count_terms,
)

from .pipeline_process import validate_run_id


SCHEMA_VERSION = 1
ELITE_ARCHIVE_SCHEMA_VERSION = 4
_ELITE_ARCHIVE_COMPATIBLE_SCHEMA_VERSIONS = frozenset({
    1,
    2,
    3,
    ELITE_ARCHIVE_SCHEMA_VERSION,
})


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _fsync_directory(path: Path) -> None:
    """Durably persist a rename in ``path`` when the platform supports it."""
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    descriptor = os.open(path, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _atomic_bytes(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-",
        dir=path.parent,
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        _fsync_directory(path.parent)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def atomic_write_bytes(path: Path, payload: bytes) -> dict[str, Any]:
    """Atomically replace a file and return the durable byte identity."""
    _atomic_bytes(path, payload)
    return {
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }


def atomic_write_json(path: Path, value: Any) -> None:
    payload = (
        json.dumps(value, ensure_ascii=False, indent=2) + "\n"
    ).encode("utf-8")
    _atomic_bytes(path, payload)


def _atomic_json(path: Path, value: Any) -> None:
    """Backward-compatible private alias for durable atomic JSON writes."""
    atomic_write_json(path, value)


def atomic_write_jsonl(
    path: Path,
    rows: Iterable[dict[str, Any]],
) -> dict[str, Any]:
    """Atomically replace a JSONL file and return its durable content identity."""
    materialized = list(rows)
    payload = "".join(
        json.dumps(row, ensure_ascii=False, default=str) + "\n"
        for row in materialized
    ).encode("utf-8")
    _atomic_bytes(path, payload)
    return {
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
        "rows": len(materialized),
    }


def append_jsonl(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(value, ensure_ascii=False, default=str) + "\n")


def _terms(row: dict[str, Any], name: str) -> list[list[int]]:
    return sorted([list(map(int, term)) for term in row.get(name, [])])


def code_key(row: dict[str, Any]) -> str:
    """Stable content key for a CSS BB code, independent of score metadata."""
    if isinstance(row.get("construction"), Mapping):
        from evaluation.construction import normalize_construction_claim

        normalized = normalize_construction_claim(dict(row))
        construction = (
            normalized.get("construction")
            if isinstance(normalized, Mapping)
            and isinstance(normalized.get("construction"), Mapping)
            else normalized
        )
        if not isinstance(construction, Mapping):
            raise ValueError("normalized construction is not an object")
        payload = json.dumps(
            {"construction": dict(construction)},
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        return hashlib.sha256(payload.encode()).hexdigest()[:20]
    ell = int(row.get("ell", 0) or 0)
    m = int(row.get("m", 0) or 0)
    defining = {
        "ell": ell,
        "m": m,
        "A_terms": _terms(row, "A_terms"),
        "B_terms": _terms(row, "B_terms"),
    }
    geometry = normalize_geometry(ell, m, row.get("geometry"))
    if geometry is not None:
        defining["geometry"] = geometry
    payload = json.dumps(defining, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()[:20]


def candidate_fom(row: dict[str, Any]) -> float:
    """Return the reported FOM for diagnostics.

    This value may be derived from a BP/OSD distance *upper* bound.  Search
    policy must use :func:`candidate_evidence_priority` or
    :func:`candidate_proven_fom` instead of ranking on this diagnostic.
    """
    value = row.get("fom", row.get("score", 0.0))
    try:
        return float(value or 0.0)
    except (TypeError, ValueError):
        return 0.0


def _positive_integer(value: Any) -> int | None:
    if isinstance(value, bool) or not isinstance(value, Integral):
        return None
    converted = int(value)
    return converted if converted > 0 else None


def candidate_terminal_negative(row: dict[str, Any]) -> bool:
    """Return whether proof-backed evidence already rejects the target.

    A scalar BP/OSD result is not durable evidence: without operator bits it
    cannot be replayed after a crash or across a trust boundary.  It therefore
    must not permanently remove a candidate from the exact-audit queue.
    """
    exact = candidate_proven_distance(row) is not None
    final_gate_excluded = bool(
        row.get("final_gate_excluded_by_upper_bound") is True
        or row.get("search_final_gate_excluded_by_upper_bound") is True
    )
    # Humanize has not yet replayed an upper-bound witness at this boundary.
    # Until a central validator binds and rechecks that certificate, even a
    # row carrying operator bits remains advisory.  Internally exact evidence
    # is the sole permanent-negative source here.
    return bool(final_gate_excluded and exact)


def candidate_proven_distance(row: dict[str, Any]) -> int | None:
    """Return an internally exact distance, never a self-declared bound.

    Certified lower bounds will be admitted here only after a central
    certificate validator can replay the X/Z coverage and bind it to the
    candidate definition.  Bare status strings or booleans are deliberately
    insufficient.
    """
    exact_raw = row.get("exact_distance")
    if exact_raw is None:
        exact_raw = row.get("d")
    exact = _positive_integer(exact_raw)
    n = _positive_integer(row.get("n"))
    reported = _positive_integer(row.get("d"))
    if (
        exact is not None
        and n is not None
        and exact <= n
        and reported == exact
        and row.get("d_is_exact") is True
        and row.get("distance_trusted") is True
        and row.get("distance_status") == "exact"
    ):
        return exact
    return None


def candidate_proven_fom(row: dict[str, Any]) -> float:
    """Compute positive fitness only from internally exact evidence."""
    distance = candidate_proven_distance(row)
    if distance is None or candidate_terminal_negative(row):
        return 0.0
    n = _positive_integer(row.get("n"))
    k = _positive_integer(row.get("k"))
    if n is None or k is None or k > n:
        return 0.0
    return k * distance * distance / n


def candidate_evidence_priority(row: dict[str, Any]) -> tuple[int, float, float, str]:
    """Upper-bound-neutral ordering for archive, audit and parent advisories.

    A terminal upper-bound witness can only lower priority.  Positive distance
    credit comes solely from exact/certified lower evidence.  Remaining ties
    use the exact encoding rate and a stable definition key; BP ``d``/FOM are
    intentionally absent.
    """
    if candidate_terminal_negative(row):
        return -1, 0.0, 0.0, code_key(row)
    n = _positive_integer(row.get("n"))
    k = _positive_integer(row.get("k"))
    rate = k / n if n is not None and k is not None and k <= n else 0.0
    proven_fom = candidate_proven_fom(row)
    return int(proven_fom > 0.0), proven_fom, rate, code_key(row)


def candidate_structural_features(
    row: dict[str, Any],
) -> dict[str, float | int]:
    """Recompute candidate-level MAP metadata from the defining terms."""

    if isinstance(row.get("construction"), Mapping):
        construction = row["construction"]
        action_id = construction.get("action_id", row.get("action_id"))
        left = construction.get("left_support", row.get("left_support"))
        right = construction.get("right_support", row.get("right_support"))
        if (
            not isinstance(action_id, str)
            or not isinstance(left, list)
            or not isinstance(right, list)
        ):
            raise ValueError("compact construction lacks action/support fields")
        from evaluation.coset_action_catalog import (
            LEGACY_CATALOG_ID,
            list_action_descriptors,
        )
        from evaluation.coset_two_block import (
            normalize_coset_two_block_construction,
        )
        from evolve.coset_search_contract import (
            ACTION_FAMILY_BINS,
            COSET_CANDIDATE_SCHEMA_VERSION_V3,
            COSET_RENDERER_V3_ID,
            COSET_REPRESENTATION_ID_V3,
            COSET_SUPPORT_ORBIT_BINS,
            canonical_json_sha256,
            coset_support_orbit_bin,
        )

        # Archive replay must remain version-aware: the live Stage-1 schema
        # points at catalog v2, but historical rows can carry an immutable v1
        # construction.  Normalize through the construction dispatcher and
        # read metadata from the catalog pinned by that construction instead
        # of silently interpreting old element IDs in the live catalog.
        canonical = normalize_coset_two_block_construction(construction)
        catalog_id = canonical.get("action_catalog_id", LEGACY_CATALOG_ID)
        descriptors = {
            descriptor["action_id"]: descriptor
            for descriptor in list_action_descriptors(catalog_id=catalog_id)
        }
        try:
            descriptor = descriptors[action_id]
            action_family_bin = ACTION_FAMILY_BINS[descriptor["bin"]]
        except (KeyError, TypeError) as exc:
            raise ValueError(
                "compact construction action metadata is unavailable"
            ) from exc
        claims_renderer_v3 = bool(
            row.get("schema_version") == COSET_CANDIDATE_SCHEMA_VERSION_V3
            or row.get("representation_id") == COSET_REPRESENTATION_ID_V3
            or row.get("renderer_descriptor_id") == COSET_RENDERER_V3_ID
        )
        if claims_renderer_v3:
            # Renderer-v3 changed the support-orbit coordinate by binding the
            # representation and explicit support split.  The mathematical
            # construction remains v2, so recover the supports from that
            # independently normalized source-bound construction, while the
            # renderer identity must be present at the candidate top level.
            # Passing the exact seven-field object through the authoritative
            # candidate normalizer also makes partial/forged v3 claims fail
            # closed instead of silently falling back to the legacy hash.
            support_orbit_bin = coset_support_orbit_bin({
                "schema_version": row.get("schema_version"),
                "representation_id": row.get("representation_id"),
                "renderer_descriptor_id": row.get(
                    "renderer_descriptor_id"
                ),
                "action_id": canonical["action_id"],
                "support_split": row.get("support_split"),
                "left_support": canonical["left_support"],
                "right_support": canonical["right_support"],
            })
        else:
            # Construction-only rows and the frozen v1/v2 search epoch retain
            # their historical supports-only coordinate for replay.
            orbit_digest = canonical_json_sha256({
                "left_support": canonical["left_support"],
                "right_support": canonical["right_support"],
            })
            support_orbit_bin = (
                int(orbit_digest[:8], 16) % COSET_SUPPORT_ORBIT_BINS
            )
        return {
            "action_family_bin": int(action_family_bin),
            "subgroup_normal": int(bool(descriptor["subgroup_normal"])),
            "support_orbit_bin": support_orbit_bin,
            "term_count": len(left) + len(right),
        }

    a_terms = _terms(row, "A_terms")
    b_terms = _terms(row, "B_terms")
    if not a_terms or not b_terms:
        raise ValueError(
            "candidate structural features require non-empty A_terms/B_terms"
        )
    return {
        "pattern_type": classify_pattern(a_terms, b_terms),
        "term_count": count_terms(a_terms, b_terms),
        "pattern_classifier_version": PATTERN_CLASSIFIER_VERSION,
    }


def archive_cell(row: dict[str, Any]) -> str:
    """Candidate-level MAP-Elites cell used across OpenEvolve rounds."""
    n = int(row.get("n", 0) or 0)
    k = int(row.get("k", 0) or 0)
    rate_bin = int(20 * k / n) if n else 0
    features = candidate_structural_features(row)
    if isinstance(row.get("construction"), Mapping):
        return (
            f"n={n}|rate={rate_bin}"
            f"|action_family={int(features['action_family_bin'])}"
            f"|normal={int(features['subgroup_normal'])}"
            f"|support_orbit={int(features['support_orbit_bin'])}"
        )
    pattern = str(features["pattern_type"])
    term_count = int(features["term_count"])
    geometry = normalize_geometry(
        int(row.get("ell", 0) or 0),
        int(row.get("m", 0) or 0),
        row.get("geometry"),
    )
    legacy_cell = (
        f"n={n}|rate={rate_bin}|pattern={pattern}|terms={term_count}"
    )
    if geometry is None:
        return legacy_cell
    twist_class = 1 if gcd(int(geometry["twist"]), int(row["m"])) == 1 else 2
    return f"{legacy_cell}|geometry_twist_class={twist_class}"


def _canonical_archive_row(original: dict[str, Any]) -> dict[str, Any]:
    row = dict(original)
    row.update(candidate_structural_features(row))
    row["candidate_key"] = code_key(row)
    row["archive_cell"] = archive_cell(row)
    return row


class EliteArchive:
    """Persistent best-per-cell archive, complementary to OpenEvolve's archive."""

    def __init__(self, path: Path):
        self.path = path
        self.cells: dict[str, dict[str, Any]] = {}
        if path.is_file():
            raw = json.loads(path.read_text())
            archive_schema_version = raw.get("schema_version")
            if archive_schema_version not in (
                _ELITE_ARCHIVE_COMPATIBLE_SCHEMA_VERSIONS
            ):
                raise ValueError("unsupported elite archive schema")
            stored_cells = raw.get("cells", {})
            if not isinstance(stored_cells, dict):
                raise ValueError("elite archive cells must be an object")
            # Stored keys and feature labels are advisory metadata, not trusted
            # identity. Rebuild them from A/B definitions on every load so a
            # v1 or forged row cannot retain a stale diversity cell.
            for original in stored_cells.values():
                if not isinstance(original, dict):
                    raise ValueError("elite archive rows must be objects")
                row = _canonical_archive_row(original)
                current = self.cells.get(row["archive_cell"])
                if (
                    current is None
                    or candidate_evidence_priority(row)
                    > candidate_evidence_priority(current)
                ):
                    self.cells[row["archive_cell"]] = row
            # Schema v3 stored renderer-v3 rows with the obsolete
            # supports-only orbit coordinate.  Persist the canonicalized,
            # best-per-new-cell replay immediately so a subsequent process
            # never observes the stale coordinate or its false cell count.
            if archive_schema_version == 3:
                self.save()

    def update(self, rows: Iterable[dict[str, Any]], round_number: int) -> list[dict[str, Any]]:
        promoted: list[dict[str, Any]] = []
        for original in rows:
            row = _canonical_archive_row(original)
            row["archive_round"] = round_number
            current = self.cells.get(row["archive_cell"])
            if (
                current is None
                or candidate_evidence_priority(row)
                > candidate_evidence_priority(current)
            ):
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
            row = _canonical_archive_row(original)
            current = cells.get(row["archive_cell"])
            if (
                current is None
                or candidate_evidence_priority(row)
                > candidate_evidence_priority(current)
            ):
                cells[row["archive_cell"]] = row
        self.cells = cells
        self.save()

    def ranked(self) -> list[dict[str, Any]]:
        return sorted(
            self.cells.values(),
            key=candidate_evidence_priority,
            reverse=True,
        )

    def save(self) -> None:
        _atomic_json(self.path, {
            "schema_version": ELITE_ARCHIVE_SCHEMA_VERSION,
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
        # A run identity is a security boundary, not a display label.  Never
        # silently rewrite it: doing so lets the config, evolution output, and
        # durable state refer to different runs.
        safe_id = validate_run_id(run_id)
        store = cls(results_dir / "humanize" / safe_id, safe_id)
        store.root.mkdir(parents=True, exist_ok=True)
        return store

    @property
    def lock_path(self) -> Path:
        return self.root / "run.lock"

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
            "round_transaction_version": 3,
            "candidate_offset": 0,
            "best_fom": 0.0,
            "best_bp_fom_upper_bound": 0.0,
            "best_exact_fom": 0.0,
            "no_improvement_rounds": 0,
            "trusted_exact_count": 0,
            "trusted_win_count": 0,
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


def read_jsonl_range(
    path: Path,
    offset: int,
    end_offset: int | None = None,
) -> tuple[list[dict[str, Any]], int, str]:
    """Read a strict, newline-terminated JSONL byte range.

    Unlike the legacy reader, malformed or partial records fail closed and do
    not advance the durable offset.  The returned digest binds the exact source
    bytes consumed by a round transaction.
    """
    if isinstance(offset, bool) or not isinstance(offset, int) or offset < 0:
        raise ValueError("JSONL offset must be a non-negative integer")
    if (
        end_offset is not None
        and (
            isinstance(end_offset, bool)
            or not isinstance(end_offset, int)
            or end_offset < offset
        )
    ):
        raise ValueError("JSONL end offset must be an integer >= offset")
    if not path.is_file():
        if offset == 0 and end_offset in (None, 0):
            return [], 0, hashlib.sha256(b"").hexdigest()
        raise ValueError(f"JSONL source is missing at non-zero offset: {path}")

    rows: list[dict[str, Any]] = []
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        size = os.fstat(stream.fileno()).st_size
        stop = size if end_offset is None else end_offset
        if offset > size or stop > size:
            raise ValueError(
                f"JSONL byte range [{offset}, {stop}) exceeds file size {size}: "
                f"{path}"
            )
        stream.seek(offset)
        while stream.tell() < stop:
            remaining = stop - stream.tell()
            raw = stream.readline(remaining)
            if not raw:
                raise ValueError(f"JSONL source ended before offset {stop}: {path}")
            if not raw.endswith(b"\n"):
                raise ValueError(
                    f"JSONL record is partial or range ends mid-record: {path}"
                )
            digest.update(raw)
            try:
                row = json.loads(raw.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ValueError(f"Invalid JSONL record in {path}: {exc}") from exc
            if not isinstance(row, dict):
                raise ValueError(f"JSONL record is not an object in {path}")
            rows.append(row)
        if stream.tell() != stop:
            raise ValueError(f"JSONL reader crossed requested offset {stop}: {path}")
        return rows, stop, digest.hexdigest()


def read_jsonl_since(path: Path, offset: int) -> tuple[list[dict[str, Any]], int]:
    """Read complete JSONL records from a byte offset and return the new offset."""
    rows, new_offset, _digest = read_jsonl_range(path, offset)
    return rows, new_offset
