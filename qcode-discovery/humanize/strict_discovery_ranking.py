"""Authenticated portfolio selection for the strict ``FOM > 12`` sidecar.

This module is intentionally outside the five-stage pipeline.  It reads the
immutable Stage 2 ranked snapshot and its sealed selection ledger, but never
writes either of them.  Heuristic distance estimates are used only to order
work; every scientific decision is delegated to the normal Stage 2 auditor.
"""

from __future__ import annotations

from dataclasses import dataclass
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import struct
import tempfile
from typing import Any, Iterable, Mapping

from .exactification_queue import (
    _stat_identity,
    _validated_stage2_source,
    canonical_sha256,
)


PORTFOLIO_SCHEMA_VERSION = 1
PORTFOLIO_GATE = "qldpc-stage2-strict-discovery-portfolio-v1"


class PortfolioSourceChangedError(RuntimeError):
    """The foreground Stage 2 ledger advanced during a portfolio scan."""


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


_RANKING_SOURCE_SHA256 = _file_sha256(Path(__file__).resolve())


def _assert_source_unchanged() -> None:
    if _file_sha256(Path(__file__).resolve()) != _RANKING_SOURCE_SHA256:
        raise RuntimeError("strict discovery ranking source changed after import")


@dataclass(frozen=True)
class PortfolioConfig:
    initial_top: int = 100
    expanded_top: int = 500
    later_batch_size: int = 500
    initial_live: int = 80
    initial_missing: int = 20

    def validate(self) -> "PortfolioConfig":
        for name in (
            "initial_top",
            "expanded_top",
            "later_batch_size",
            "initial_live",
            "initial_missing",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise ValueError(f"{name} must be a positive integer")
        if self.initial_live + self.initial_missing != self.initial_top:
            raise ValueError("initial lane quotas must sum to initial_top")
        if self.expanded_top < self.initial_top:
            raise ValueError("expanded_top must be at least initial_top")
        return self

    @classmethod
    def from_mapping(cls, value: Mapping[str, Any] | None) -> "PortfolioConfig":
        if value is None:
            return cls().validate()
        allowed = {field.name for field in __import__("dataclasses").fields(cls)}
        unknown = set(value) - allowed
        if unknown:
            raise ValueError(f"unknown portfolio fields: {sorted(unknown)}")
        return cls(**{name: value[name] for name in value}).validate()


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def _strict_required_distance(n: int, k: int) -> int:
    """Return the least integer d satisfying ``k*d*d > 12*n``."""

    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer")
    if isinstance(k, bool) or not isinstance(k, int) or k < 1:
        raise ValueError("k must be a positive integer")
    return math.isqrt((12 * n) // k) + 1


def _source_stability_token(
    validated: Mapping[str, Any],
    snapshot: Any,
    source_data: Mapping[str, Any],
) -> dict[str, Any]:
    """Bind every foreground-ledger coordinate that can overlap this scan."""

    source = source_data.get("source")
    completed = source_data.get("completed")
    pending = validated.get("pending")
    if not isinstance(source, Mapping) or not isinstance(completed, Mapping):
        raise ValueError("validated Stage 2 source metadata is malformed")
    if pending is not None and not isinstance(pending, Mapping):
        raise ValueError("validated Stage 2 pending page is malformed")
    return {
        "snapshot_identity_sha256": source.get(
            "snapshot_identity_sha256",
            validated.get("snapshot_identity_sha256"),
        ),
        "ledger_progress_sha256": source.get("ledger_progress_sha256"),
        "cursor": validated.get("cursor"),
        "pending_sha256": (
            canonical_sha256(dict(pending))
            if isinstance(pending, Mapping)
            else None
        ),
        "completed_digests_sha256": canonical_sha256(
            sorted(str(digest) for digest in completed)
        ),
        "snapshot_rows": getattr(snapshot, "rows", None),
        "eligible_rows": getattr(snapshot, "eligible_rows", None),
    }


def _row_digest(row: Mapping[str, Any]) -> str:
    novelty = row.get("structural_novelty")
    triage = row.get("triage_identity")
    candidates = [
        novelty.get("canonical_digest") if isinstance(novelty, Mapping) else None,
        triage.get("canonical_digest") if isinstance(triage, Mapping) else None,
        row.get("canonical_digest"),
    ]
    values = {str(item) for item in candidates if isinstance(item, str)}
    values = {
        item
        for item in values
        if len(item) == 64 and all(char in "0123456789abcdef" for char in item)
    }
    if len(values) != 1:
        raise ValueError("ranked snapshot row has an ambiguous canonical digest")
    return values.pop()


def _iter_authenticated_rows(snapshot: Any, start: int) -> Iterable[tuple[int, dict[str, Any]]]:
    if start < 0 or start > snapshot.eligible_rows:
        raise ValueError("selection cursor is outside the ranked snapshot")
    with (
        snapshot.snapshot_path.open("rb") as ranked_stream,
        snapshot.offsets_path.open("rb") as offsets_stream,
    ):
        fcntl.flock(ranked_stream.fileno(), fcntl.LOCK_SH)
        fcntl.flock(offsets_stream.fileno(), fcntl.LOCK_SH)
        try:
            if (
                _stat_identity(os.fstat(ranked_stream.fileno())) != snapshot.snapshot_stat
                or _stat_identity(os.fstat(offsets_stream.fileno())) != snapshot.offsets_stat
            ):
                raise ValueError("ranked snapshot changed before portfolio scan")
            for chunk in snapshot.chunks:
                chunk_start = int(chunk["start_row"])
                chunk_end = min(int(chunk["end_row"]), int(snapshot.eligible_rows))
                if chunk_end <= start or chunk_start >= snapshot.eligible_rows:
                    continue
                snapshot_start = int(chunk["snapshot_start"])
                snapshot_end = int(chunk["snapshot_end"])
                offsets_start = int(chunk["offsets_start"])
                offsets_end = int(chunk["offsets_end"])
                ranked_stream.seek(snapshot_start)
                payload = ranked_stream.read(snapshot_end - snapshot_start)
                offsets_stream.seek(offsets_start)
                encoded_offsets = offsets_stream.read(offsets_end - offsets_start)
                if (
                    len(payload) != snapshot_end - snapshot_start
                    or hashlib.sha256(payload).hexdigest() != chunk["snapshot_sha256"]
                    or len(encoded_offsets) != offsets_end - offsets_start
                    or hashlib.sha256(encoded_offsets).hexdigest() != chunk["offsets_sha256"]
                ):
                    raise ValueError("ranked snapshot chunk hash mismatch")
                count = int(chunk["end_row"]) - chunk_start + 1
                offsets = struct.unpack(f">{count}Q", encoded_offsets)
                if (
                    offsets[0] != snapshot_start
                    or offsets[-1] != snapshot_end
                    or any(left >= right for left, right in zip(offsets, offsets[1:]))
                ):
                    raise ValueError("ranked snapshot offsets are inconsistent")
                for index in range(max(start, chunk_start), chunk_end):
                    local = index - chunk_start
                    left = offsets[local] - snapshot_start
                    right = offsets[local + 1] - snapshot_start
                    raw = payload[left:right]
                    if not raw.endswith(b"\n"):
                        raise ValueError("ranked snapshot contains a partial row")
                    try:
                        row = json.loads(raw)
                    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                        raise ValueError("ranked snapshot row is malformed") from exc
                    if not isinstance(row, dict):
                        raise ValueError("ranked snapshot row is not an object")
                    yield index, row
            if (
                _stat_identity(os.fstat(ranked_stream.fileno())) != snapshot.snapshot_stat
                or _stat_identity(os.fstat(offsets_stream.fileno())) != snapshot.offsets_stat
            ):
                raise ValueError("ranked snapshot changed during portfolio scan")
        finally:
            fcntl.flock(offsets_stream.fileno(), fcntl.LOCK_UN)
            fcntl.flock(ranked_stream.fileno(), fcntl.LOCK_UN)


def _relation(row: Mapping[str, Any]) -> str:
    raw = str(row.get("relation_type") or row.get("algebraic_relation_type") or "unspecified").lower()
    for name in ("unstructured", "asymmetric", "shared", "affine", "complementary"):
        if name in raw:
            return name
    return raw


def _geometry(row: Mapping[str, Any]) -> str:
    geometry = row.get("geometry")
    if isinstance(geometry, Mapping) and isinstance(geometry.get("family"), str):
        return str(geometry["family"])
    return "unspecified"


def _pattern(row: Mapping[str, Any]) -> str:
    value = row.get("pattern_type")
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return str(int(value))
    return str(value or "unspecified")


def _candidate(index: int, row: Mapping[str, Any], blocked: set[str]) -> dict[str, Any] | None:
    digest = _row_digest(row)
    if digest in blocked or row.get("C_terms") or row.get("D_terms"):
        return None
    novelty = row.get("structural_novelty")
    static = row.get("static_eligibility")
    structural = row.get("stage2_structural_screen")
    report = static.get("logical_basis_upper_bound") if isinstance(static, Mapping) else None
    if (
        not isinstance(novelty, Mapping)
        or novelty.get("checked") is not True
        or novelty.get("novel") is not True
        or not isinstance(static, Mapping)
        or static.get("eligible") is not True
        or not isinstance(structural, Mapping)
        or structural.get("status") != "COMPLETE"
        or not isinstance(report, Mapping)
        or report.get("available") is not True
        or report.get("method") != "replayed-minimum-symplectic-basis-row"
    ):
        return None
    n, k, upper = row.get("n"), row.get("k"), report.get("upper_bound")
    if any(isinstance(value, bool) or not isinstance(value, int) or value < 1 for value in (n, k, upper)):
        return None
    required = _strict_required_distance(n, k)
    if upper < required:
        return None
    advisory = row.get("distance_upper_bound")
    if isinstance(advisory, bool) or not isinstance(advisory, int) or advisory < 1:
        lane = "BP_MISSING"
        scheduling_upper = upper
        advisory = None
    elif k * advisory * advisory > 12 * n:
        lane = "BP_LIVE"
        scheduling_upper = advisory
    else:
        lane = "BP_DEAD"
        scheduling_upper = advisory
    occurrence = row.get("generator_occurrence_count")
    occurrence = occurrence if isinstance(occurrence, int) and not isinstance(occurrence, bool) else 0
    return {
        "canonical_digest": digest,
        "snapshot_index": index,
        "n": n,
        "k": k,
        "required_distance": required,
        "d_req": required,
        "cutoff": required - 1,
        "basis_upper_bound": upper,
        "advisory_upper_bound": advisory,
        "advisory_source": row.get("distance_upper_bound_source"),
        "scheduling_only": True,
        "caveats": [
            "distance and basis upper bounds schedule work but never prove a win",
            "only the strict Stage 2 threshold auditor may promote this candidate",
        ],
        "lane": lane,
        "relation": _relation(row),
        "pattern": _pattern(row),
        "geometry": _geometry(row),
        "generator_occurrence_count": occurrence,
        "rank_key": [
            required,
            n,
            k,
            -min(max(scheduling_upper - required, 0), 2),
            -occurrence,
            digest,
        ],
        "row": dict(row),
    }


def _diverse(items: list[dict[str, Any]], limit: int, *, lane: str) -> list[dict[str, Any]]:
    if limit <= 0:
        return []
    caps = (
        {"pair": 10, "relation": 40, "pattern": 56, "geometry": 64}
        if lane == "BP_LIVE"
        else {"pair": 4, "relation": 10, "pattern": 14, "geometry": 16}
    )
    selected: list[dict[str, Any]] = []
    seen: set[str] = set()
    counts: dict[str, dict[Any, int]] = {name: {} for name in caps}

    def can_add(item: Mapping[str, Any]) -> bool:
        values = {
            "pair": (item["n"], item["k"]),
            "relation": item["relation"],
            "pattern": item["pattern"],
            "geometry": item["geometry"],
        }
        return all(counts[name].get(value, 0) < caps[name] for name, value in values.items())

    def add(item: dict[str, Any]) -> None:
        digest = str(item["canonical_digest"])
        if digest in seen:
            return
        seen.add(digest)
        selected.append(item)
        for name, value in {
            "pair": (item["n"], item["k"]),
            "relation": item["relation"],
            "pattern": item["pattern"],
            "geometry": item["geometry"],
        }.items():
            counts[name][value] = counts[name].get(value, 0) + 1

    # Seed every relation before filling by deterministic cost order.
    for relation in sorted({str(item["relation"]) for item in items}):
        first = next((item for item in items if item["relation"] == relation), None)
        if first is not None and len(selected) < limit and can_add(first):
            add(first)
    for item in items:
        if len(selected) >= limit:
            break
        if can_add(item):
            add(item)
    # Caps are diversity preferences, never a reason to underfill a batch.
    for item in items:
        if len(selected) >= limit:
            break
        add(item)
    return selected


def _interleave(live: list[dict[str, Any]], missing: list[dict[str, Any]]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    left = list(live)
    right = list(missing)
    while left or right:
        for _ in range(4):
            if left:
                result.append(left.pop(0))
        if right:
            result.append(right.pop(0))
        if not left:
            result.extend(right)
            break
        if not right:
            result.extend(left)
            break
    return result


def discover_portfolio(ledger_path: Path, config: PortfolioConfig = PortfolioConfig()) -> dict[str, Any]:
    config = config.validate()
    _assert_source_unchanged()
    ledger_path = Path(ledger_path)
    validated, snapshot, source_data = _validated_stage2_source(ledger_path)
    source_stability = _source_stability_token(validated, snapshot, source_data)
    blocked = set(source_data["completed"])
    pending = validated.get("pending")
    if isinstance(pending, Mapping):
        # ``pending`` is itself a sealed selection page in ledger v2.  Accept
        # the older nested test fixture shape as well, but never enqueue work
        # the foreground Stage 2 process is already solving.
        page = pending.get("page") if isinstance(pending.get("page"), Mapping) else pending
        blocked.update(str(item) for item in page.get("selected_digests", []))
    lanes: dict[str, list[dict[str, Any]]] = {name: [] for name in ("BP_LIVE", "BP_MISSING", "BP_DEAD")}
    for index, row in _iter_authenticated_rows(snapshot, int(validated["cursor"])):
        item = _candidate(index, row, blocked)
        if item is not None:
            lanes[item["lane"]].append(item)
    post_validated, post_snapshot, post_source_data = _validated_stage2_source(
        ledger_path
    )
    if _source_stability_token(
        post_validated,
        post_snapshot,
        post_source_data,
    ) != source_stability:
        raise PortfolioSourceChangedError(
            "Stage 2 ledger changed during portfolio scan; retry from a fresh source"
        )
    _assert_source_unchanged()
    for values in lanes.values():
        values.sort(key=lambda item: tuple(item["rank_key"]))

    initial_live = _diverse(lanes["BP_LIVE"], min(config.initial_live, len(lanes["BP_LIVE"])), lane="BP_LIVE")
    initial_missing = _diverse(
        lanes["BP_MISSING"],
        min(config.initial_missing, len(lanes["BP_MISSING"])),
        lane="BP_MISSING",
    )
    initial = _interleave(initial_live, initial_missing)[: config.initial_top]
    used = {str(item["canonical_digest"]) for item in initial}
    ordered_rest = [
        item
        for lane in ("BP_LIVE", "BP_MISSING", "BP_DEAD")
        for item in lanes[lane]
        if str(item["canonical_digest"]) not in used
    ]
    expanded = initial + ordered_rest[: max(0, config.expanded_top - len(initial))]
    used_expanded = {str(item["canonical_digest"]) for item in expanded}
    tail = [item for item in ordered_rest if str(item["canonical_digest"]) not in used_expanded]
    batches = [initial]
    if len(expanded) > len(initial):
        batches.append(expanded[len(initial) :])
    batches.extend(
        tail[index : index + config.later_batch_size]
        for index in range(0, len(tail), config.later_batch_size)
    )
    batches = [batch for batch in batches if batch]
    source = {
        **source_data["source"],
        "portfolio_cursor": int(validated["cursor"]),
        "portfolio_pending_sha256": (
            pending.get("page_sha256") if isinstance(pending, Mapping) else None
        ),
        "blocked_digests": len(blocked),
        "eligible_remaining_rows": int(snapshot.eligible_rows) - int(validated["cursor"]),
        "post_scan_revalidated": True,
        "source_stability_sha256": canonical_sha256(source_stability),
    }
    result = {
        "schema_version": PORTFOLIO_SCHEMA_VERSION,
        "gate": PORTFOLIO_GATE,
        "producer": {
            "module": "humanize.strict_discovery_ranking",
            "source_sha256": _RANKING_SOURCE_SHA256,
        },
        "publication_certificate": False,
        "pipeline_promotion": False,
        "target_mode": "scalar-fom-strict-v1",
        "target_predicate": "k*d*d > 12*n",
        "scheduling_policy": {
            "heuristic_fields_are_proof": False,
            "basis_role": "strict-feasibility-filter-and-capped-tiebreak",
            "distance_upper_role": "lane-and-capped-tiebreak-only",
            "caveat": "absence or magnitude of an advisory bound never certifies a win",
        },
        "source": source,
        "config": config.__dict__,
        "lane_counts": {name: len(values) for name, values in lanes.items()},
        "candidate_count": sum(len(values) for values in lanes.values()),
        "batches": [
            {
                "sequence": sequence,
                "count": len(batch),
                "digests": [item["canonical_digest"] for item in batch],
                "lanes": {name: sum(item["lane"] == name for item in batch) for name in lanes},
            }
            for sequence, batch in enumerate(batches)
        ],
        "items": [
            {
                **{key: value for key, value in item.items() if key != "row"},
                "portfolio_rank": rank,
            }
            for rank, item in enumerate(
                (item for batch in batches for item in batch), start=1
            )
        ],
    }
    result["portfolio_sha256"] = canonical_sha256(result)
    result["_batch_rows"] = [[item["row"] for item in batch] for batch in batches]
    return result


def write_portfolio(portfolio: Mapping[str, Any], output_dir: Path) -> dict[str, Any]:
    output_dir = Path(output_dir)
    batch_rows = portfolio.get("_batch_rows")
    if not isinstance(batch_rows, list):
        raise ValueError("portfolio lacks batch rows")
    manifest = {key: value for key, value in portfolio.items() if key != "_batch_rows"}
    expected = manifest.get("portfolio_sha256")
    unsealed = {key: value for key, value in manifest.items() if key != "portfolio_sha256"}
    if expected != canonical_sha256(unsealed):
        raise ValueError("portfolio seal is invalid")
    output_dir.mkdir(parents=True, exist_ok=True)
    path = output_dir / "ranked-input.jsonl"
    temporary = output_dir / f".{path.name}.{os.getpid()}.{next(tempfile._get_candidate_names())}.tmp"
    digest = hashlib.sha256()
    rows_written = 0
    bytes_written = 0
    try:
        descriptor = os.open(
            temporary,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        with os.fdopen(descriptor, "wb") as stream:
            for rows in batch_rows:
                for row in rows:
                    payload = _canonical_bytes(row) + b"\n"
                    stream.write(payload)
                    digest.update(payload)
                    rows_written += 1
                    bytes_written += len(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
    manifest["ranked_input"] = {
        "path": str(path.resolve()),
        "bytes": bytes_written,
        "rows": rows_written,
        "sha256": digest.hexdigest(),
        "payload_kind": "authenticated-ranked-snapshot-rows-in-portfolio-order",
    }
    manifest.pop("portfolio_sha256", None)
    manifest["portfolio_sha256"] = canonical_sha256(manifest)
    _atomic_write(output_dir / "portfolio.json", _canonical_bytes(manifest) + b"\n")
    return manifest


__all__ = [
    "PORTFOLIO_GATE",
    "PortfolioConfig",
    "PortfolioSourceChangedError",
    "discover_portfolio",
    "write_portfolio",
]
