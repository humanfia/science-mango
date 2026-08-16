"""Tests for the authenticated strict-FOM discovery portfolio."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import struct
from types import SimpleNamespace
from typing import Any

import pytest

from humanize import strict_discovery_ranking as ranking


def _digest(index: int) -> str:
    return f"{index:064x}"


def _row(
    index: int,
    *,
    bp_upper: int | None,
    n: int = 12,
    k: int = 12,
    basis_upper: int = 10,
    relation: str = "unstructured",
    pattern: str = "pattern3",
    geometry: str | None = "twisted_torus",
) -> dict[str, Any]:
    digest = _digest(index)
    row: dict[str, Any] = {
        "canonical_digest": digest,
        "n": n,
        "k": k,
        "structural_novelty": {
            "checked": True,
            "novel": True,
            "canonical_digest": digest,
        },
        "stage2_structural_screen": {"status": "COMPLETE"},
        "static_eligibility": {
            "checked": True,
            "eligible": True,
            "logical_basis_upper_bound": {
                "available": True,
                "method": "replayed-minimum-symplectic-basis-row",
                "upper_bound": basis_upper,
            },
        },
        "relation_type": relation,
        "pattern_type": pattern,
        "generator_occurrence_count": index % 7,
    }
    if geometry is not None:
        row["geometry"] = {"family": geometry, "twist": 1}
    if bp_upper is not None:
        row["distance_upper_bound"] = bp_upper
        row["distance_upper_bound_source"] = "bp_osd"
    return row


def test_strict_required_distance_uses_integer_boundary() -> None:
    # 24 * 12^2 / 288 == 12, so strict discovery needs d=13.
    assert ranking._strict_required_distance(288, 24) == 13
    assert ranking._strict_required_distance(210, 42) == 8
    assert ranking._strict_required_distance(1, 12) == 2
    with pytest.raises(ValueError, match="positive integer"):
        ranking._strict_required_distance(True, 2)
    with pytest.raises(ValueError, match="positive integer"):
        ranking._strict_required_distance(2, 0)


def test_candidate_lanes_are_scheduling_only_and_basis_gated() -> None:
    live = ranking._candidate(10, _row(1, bp_upper=5), set())
    missing = ranking._candidate(11, _row(2, bp_upper=None), set())
    dead = ranking._candidate(12, _row(3, bp_upper=3), set())

    assert live is not None and live["lane"] == "BP_LIVE"
    assert missing is not None and missing["lane"] == "BP_MISSING"
    assert dead is not None and dead["lane"] == "BP_DEAD"
    assert live["required_distance"] == live["d_req"] == 4
    assert live["cutoff"] == 3
    assert live["scheduling_only"] is True
    assert "never prove" in " ".join(live["caveats"]).lower()
    assert missing["advisory_upper_bound"] is None

    boundary = ranking._candidate(
        13,
        _row(4, bp_upper=12, n=288, k=24, basis_upper=20),
        set(),
    )
    assert boundary is not None
    assert boundary["required_distance"] == 13
    assert boundary["lane"] == "BP_DEAD"

    stale = _row(5, bp_upper=5)
    stale["static_eligibility"]["logical_basis_upper_bound"]["method"] = "legacy-hint"
    assert ranking._candidate(14, stale, set()) is None

    excluded = _row(6, bp_upper=5, basis_upper=3)
    assert ranking._candidate(15, excluded, set()) is None
    assert ranking._candidate(15, _row(7, bp_upper=5), {_digest(7)}) is None


def test_lane_sort_does_not_reward_uncapped_raw_upper() -> None:
    modest_row = _row(20, bp_upper=None, basis_upper=6)
    loose_row = _row(21, bp_upper=None, basis_upper=10_000)
    modest_row["generator_occurrence_count"] = 0
    loose_row["generator_occurrence_count"] = 0
    modest = ranking._candidate(1, modest_row, set())
    loose = ranking._candidate(2, loose_row, set())
    assert modest is not None and loose is not None
    # Both bounds have at least two steps of scheduling headroom.  The huge,
    # mathematically loose basis upper therefore cannot dominate the digest
    # tie-break or change the cost coordinates.
    assert modest["rank_key"][:-1] == loose["rank_key"][:-1]
    assert sorted([loose, modest], key=lambda item: tuple(item["rank_key"])) == [
        modest,
        loose,
    ]


def test_lane_sort_uses_k_ascending_after_required_distance_and_n() -> None:
    smaller_k_row = _row(100, bp_upper=20, n=100, k=10, basis_upper=20)
    larger_k_row = _row(1, bp_upper=20, n=100, k=11, basis_upper=20)
    smaller_k_row["generator_occurrence_count"] = 0
    larger_k_row["generator_occurrence_count"] = 0
    smaller_k = ranking._candidate(1, smaller_k_row, set())
    larger_k = ranking._candidate(2, larger_k_row, set())

    assert smaller_k is not None and larger_k is not None
    assert smaller_k["required_distance"] == larger_k["required_distance"] == 11
    assert smaller_k["rank_key"][2] == 10
    assert larger_k["rank_key"][2] == 11
    assert sorted(
        [larger_k, smaller_k], key=lambda item: tuple(item["rank_key"])
    ) == [smaller_k, larger_k]


def test_authenticated_iterator_checks_chunks_and_cursor(tmp_path: Path) -> None:
    rows = [_row(index, bp_upper=5) for index in range(3)]
    payloads = [
        json.dumps(row, sort_keys=True, separators=(",", ":")).encode() + b"\n"
        for row in rows
    ]
    payload = b"".join(payloads)
    offsets = [0]
    for encoded in payloads:
        offsets.append(offsets[-1] + len(encoded))
    encoded_offsets = struct.pack(f">{len(offsets)}Q", *offsets)
    snapshot_path = tmp_path / "snapshot.jsonl"
    offsets_path = tmp_path / "snapshot.offsets"
    snapshot_path.write_bytes(payload)
    offsets_path.write_bytes(encoded_offsets)
    snapshot = SimpleNamespace(
        eligible_rows=3,
        snapshot_path=snapshot_path,
        offsets_path=offsets_path,
        snapshot_stat=ranking._stat_identity(os.stat(snapshot_path)),
        offsets_stat=ranking._stat_identity(os.stat(offsets_path)),
        chunks=[{
            "start_row": 0,
            "end_row": 3,
            "snapshot_start": 0,
            "snapshot_end": len(payload),
            "offsets_start": 0,
            "offsets_end": len(encoded_offsets),
            "snapshot_sha256": hashlib.sha256(payload).hexdigest(),
            "offsets_sha256": hashlib.sha256(encoded_offsets).hexdigest(),
        }],
    )

    selected = list(ranking._iter_authenticated_rows(snapshot, 1))
    assert [(index, row["canonical_digest"]) for index, row in selected] == [
        (1, _digest(1)),
        (2, _digest(2)),
    ]
    with pytest.raises(ValueError, match="outside"):
        list(ranking._iter_authenticated_rows(snapshot, 4))

    snapshot.chunks[0]["snapshot_sha256"] = "0" * 64
    with pytest.raises(ValueError, match="chunk hash"):
        list(ranking._iter_authenticated_rows(snapshot, 0))


def test_portfolio_has_80_20_head_all_live_expansion_then_missing_and_dead(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    relations = [
        "unstructured",
        "asymmetric_anchor",
        "shared_anchor_coset",
        "affine_orbit",
        "complementary_diagonal",
    ]
    rows: list[dict[str, Any]] = []
    for index in range(206):
        rows.append(
            _row(
                index + 1,
                bp_upper=5,
                relation=relations[index % len(relations)],
                pattern=f"pattern{3 + index % 2}",
            )
        )
    for index in range(400):
        marker = 1_000 + index
        rows.append(
            _row(
                marker,
                bp_upper=None,
                relation=relations[index % len(relations)],
                pattern=f"pattern{3 + index % 2}",
                geometry=None if index % 3 == 0 else "twisted_torus",
            )
        )
    for index in range(10):
        rows.append(_row(2_000 + index, bp_upper=3))

    snapshot = SimpleNamespace(eligible_rows=50 + len(rows))
    validated = {"cursor": 50, "pending": None}
    source_data = {
        "completed": {},
        "source": {
            "snapshot_identity_sha256": "a" * 64,
            "ledger_progress_sha256": "b" * 64,
        },
    }
    monkeypatch.setattr(
        ranking,
        "_validated_stage2_source",
        lambda _path: (validated, snapshot, source_data),
    )
    monkeypatch.setattr(
        ranking,
        "_iter_authenticated_rows",
        lambda _snapshot, start: enumerate(rows, start=start),
    )

    portfolio = ranking.discover_portfolio(Path("ledger.json"))
    assert portfolio["lane_counts"] == {
        "BP_LIVE": 206,
        "BP_MISSING": 400,
        "BP_DEAD": 10,
    }
    assert portfolio["candidate_count"] == 616
    items = portfolio["items"]
    assert [item["lane"] for item in items[:10]] == [
        "BP_LIVE",
        "BP_LIVE",
        "BP_LIVE",
        "BP_LIVE",
        "BP_MISSING",
    ] * 2
    assert {item["relation"] for item in items[:100]} == {
        "unstructured",
        "asymmetric",
        "shared",
        "affine",
        "complementary",
    }
    assert sum(item["lane"] == "BP_LIVE" for item in items[:100]) == 80
    assert sum(item["lane"] == "BP_MISSING" for item in items[:100]) == 20
    assert sum(item["lane"] == "BP_LIVE" for item in items[:500]) == 206
    assert sum(item["lane"] == "BP_MISSING" for item in items[:500]) == 294
    assert all(item["lane"] == "BP_MISSING" for item in items[500:606])
    assert all(item["lane"] == "BP_DEAD" for item in items[606:])
    assert [item["portfolio_rank"] for item in items] == list(range(1, 617))
    assert all(item["scheduling_only"] is True for item in items)
    assert portfolio["publication_certificate"] is False
    assert portfolio["pipeline_promotion"] is False
    assert portfolio["source"]["post_scan_revalidated"] is True
    assert len(portfolio["producer"]["source_sha256"]) == 64

    manifest_without_rows = {
        key: value for key, value in portfolio.items() if key != "_batch_rows"
    }
    seal = manifest_without_rows.pop("portfolio_sha256")
    assert seal == ranking.canonical_sha256(manifest_without_rows)


def test_discovery_excludes_completed_and_pending_ack_digests(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    rows = [
        _row(1, bp_upper=5),
        _row(2, bp_upper=5),
        _row(3, bp_upper=5),
        _row(4, bp_upper=None),
    ]
    snapshot = SimpleNamespace(eligible_rows=14)
    validated = {
        "cursor": 10,
        "pending": {
            "page_sha256": "c" * 64,
            "page": {"selected_digests": [_digest(2)]},
        },
    }
    source_data = {
        "completed": {_digest(1): {"sequence": 0}},
        "source": {"snapshot_identity_sha256": "a" * 64},
    }
    monkeypatch.setattr(
        ranking,
        "_validated_stage2_source",
        lambda _path: (validated, snapshot, source_data),
    )
    monkeypatch.setattr(
        ranking,
        "_iter_authenticated_rows",
        lambda _snapshot, start: enumerate(rows, start=start),
    )
    config = ranking.PortfolioConfig(
        initial_top=2,
        expanded_top=2,
        later_batch_size=2,
        initial_live=1,
        initial_missing=1,
    )

    portfolio = ranking.discover_portfolio(Path("ledger.json"), config)

    assert portfolio["source"]["blocked_digests"] == 2
    assert portfolio["source"]["portfolio_pending_sha256"] == "c" * 64
    assert [item["canonical_digest"] for item in portfolio["items"]] == [
        _digest(3),
        _digest(4),
    ]


@pytest.mark.parametrize("changed_coordinate", ["progress", "cursor", "pending", "identity"])
def test_discovery_fails_closed_if_stage2_source_changes_during_scan(
    monkeypatch: pytest.MonkeyPatch,
    changed_coordinate: str,
) -> None:
    snapshot = SimpleNamespace(eligible_rows=1, rows=1)
    initial_validated: dict[str, Any] = {"cursor": 0, "pending": None}
    later_validated: dict[str, Any] = {"cursor": 0, "pending": None}
    initial_source = {
        "completed": {},
        "source": {
            "snapshot_identity_sha256": "a" * 64,
            "ledger_progress_sha256": "b" * 64,
        },
    }
    later_source = {
        "completed": {},
        "source": dict(initial_source["source"]),
    }
    if changed_coordinate == "progress":
        later_source["source"]["ledger_progress_sha256"] = "c" * 64
    elif changed_coordinate == "cursor":
        later_validated["cursor"] = 1
    elif changed_coordinate == "pending":
        later_validated["pending"] = {
            "page_sha256": "d" * 64,
            "selected_digests": [_digest(99)],
        }
    else:
        later_source["source"]["snapshot_identity_sha256"] = "e" * 64
    sources = iter(
        [
            (initial_validated, snapshot, initial_source),
            (later_validated, snapshot, later_source),
        ]
    )
    monkeypatch.setattr(
        ranking,
        "_validated_stage2_source",
        lambda _path: next(sources),
    )
    monkeypatch.setattr(
        ranking,
        "_iter_authenticated_rows",
        lambda _snapshot, start: iter([(start, _row(1, bp_upper=5))]),
    )
    config = ranking.PortfolioConfig(
        initial_top=2,
        expanded_top=2,
        later_batch_size=2,
        initial_live=1,
        initial_missing=1,
    )

    with pytest.raises(ranking.PortfolioSourceChangedError, match="retry"):
        ranking.discover_portfolio(Path("ledger.json"), config)


def test_write_portfolio_hashes_raw_authenticated_batches(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    rows = [_row(index + 1, bp_upper=5) for index in range(5)]
    snapshot = SimpleNamespace(eligible_rows=len(rows))
    monkeypatch.setattr(
        ranking,
        "_validated_stage2_source",
        lambda _path: (
            {"cursor": 0, "pending": None},
            snapshot,
            {"completed": {}, "source": {}},
        ),
    )
    monkeypatch.setattr(
        ranking,
        "_iter_authenticated_rows",
        lambda _snapshot, start: enumerate(rows, start=start),
    )
    config = ranking.PortfolioConfig(
        initial_top=2,
        expanded_top=4,
        later_batch_size=2,
        initial_live=1,
        initial_missing=1,
    )
    portfolio = ranking.discover_portfolio(Path("ledger.json"), config)
    manifest = ranking.write_portfolio(portfolio, tmp_path / "export")

    entry = manifest["ranked_input"]
    path = Path(entry["path"])
    payload = path.read_bytes()
    assert entry["sha256"] == hashlib.sha256(payload).hexdigest()
    assert entry["bytes"] == len(payload)
    assert entry["rows"] == len(payload.splitlines()) == 5
    exported = [json.loads(line) for line in payload.splitlines()]
    assert [row["canonical_digest"] for row in exported] == [
        item["canonical_digest"] for item in portfolio["items"]
    ]
    assert sorted(exported, key=lambda row: row["canonical_digest"]) == sorted(
        rows, key=lambda row: row["canonical_digest"]
    )
    unsigned = dict(manifest)
    seal = unsigned.pop("portfolio_sha256")
    assert seal == ranking.canonical_sha256(unsigned)
    persisted = json.loads((tmp_path / "export" / "portfolio.json").read_text())
    assert persisted == manifest
