"""Tests for durable lease-based campaign deduplication."""

from __future__ import annotations

import sqlite3
from concurrent.futures import ProcessPoolExecutor
from datetime import datetime, timedelta, timezone
from multiprocessing import get_context

import pytest

from evaluation.campaign_dedup import CampaignDedup


def _claim_in_process(payload: tuple[str, str]) -> bool:
    path, source = payload
    with CampaignDedup(
        path, busy_timeout_ms=10_000, owner_id=source,
    ) as dedup:
        return dedup.claim(
            "a" * 64, source=source, metadata={"worker": source},
        )


def test_owner_renews_unfinished_and_completed_is_permanent(tmp_path):
    path = tmp_path / "campaign.sqlite3"
    now = [datetime(2026, 7, 26, tzinfo=timezone.utc)]
    clock = lambda: now[0]
    with CampaignDedup(path, owner_id="owner-a", clock=clock) as first:
        assert first.claim(
            "digest-a", source="shard-00", metadata={"trial": 7},
        )
        assert first.claim("digest-a", source="shard-00")
        with CampaignDedup(path, owner_id="owner-b", clock=clock) as other:
            assert not other.claim("digest-a", source="shard-01")
            assert first.complete("digest-a")
            assert not other.claim("digest-a", source="shard-01")

        record = first.get("digest-a")
        assert record["first_source"] == "shard-00"
        assert record["first_metadata"] == {"trial": 7}
        assert record["lifecycle_state"] == "completed"
        assert record["lease_owner"] is None
        assert record["lease_expires_utc"] is None
        assert record["claim_count"] == 4
        assert first.stats() == {
            "schema_version": 2,
            "unique_candidates": 1,
            "total_claims": 4,
            "duplicate_claims": 3,
            "leased_candidates": 0,
            "completed_candidates": 1,
            "sources": [
                {
                    "source": "shard-00",
                    "unique_candidates": 1,
                    "total_claims": 2,
                },
                {
                    "source": "shard-01",
                    "unique_candidates": 1,
                    "total_claims": 2,
                },
            ],
        }


def test_expired_unfinished_lease_can_be_reclaimed(tmp_path):
    path = tmp_path / "campaign.sqlite3"
    now = [datetime(2026, 7, 26, tzinfo=timezone.utc)]
    clock = lambda: now[0]
    with CampaignDedup(
        path, owner_id="owner-a", lease_seconds=60, clock=clock,
    ) as first, CampaignDedup(
        path, owner_id="owner-b", lease_seconds=60, clock=clock,
    ) as second:
        assert first.claim("digest", source="shard-a")
        assert not second.claim("digest", source="shard-b")
        now[0] += timedelta(seconds=61)
        assert second.claim("digest", source="shard-b")
        assert first.complete("digest") is False
        assert second.complete("digest") is True
        now[0] += timedelta(days=1)
        assert first.claim("digest", source="shard-a") is False


def test_claim_is_atomic_across_processes(tmp_path):
    path = str(tmp_path / "concurrent.sqlite3")
    payloads = [(path, f"owner-{index}") for index in range(32)]
    context = get_context("spawn")
    with ProcessPoolExecutor(max_workers=4, mp_context=context) as executor:
        first_claims = list(executor.map(_claim_in_process, payloads))

    assert sum(first_claims) == 1
    with CampaignDedup(path) as dedup:
        record = dedup.get("a" * 64)
        assert record["claim_count"] == len(payloads)
        assert record["lifecycle_state"] == "leased"
        assert dedup.stats()["leased_candidates"] == 1


def test_v1_database_migrates_legacy_claims_as_completed(tmp_path):
    path = tmp_path / "legacy.sqlite3"
    connection = sqlite3.connect(path)
    connection.executescript(
        """
        CREATE TABLE campaign_dedup_meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
        INSERT INTO campaign_dedup_meta VALUES ('schema_version', '1');
        CREATE TABLE candidates (
            canonical_digest TEXT PRIMARY KEY,
            first_source TEXT NOT NULL,
            first_seen_utc TEXT NOT NULL,
            first_metadata_json TEXT NOT NULL,
            last_source TEXT NOT NULL,
            last_seen_utc TEXT NOT NULL,
            claim_count INTEGER NOT NULL DEFAULT 0
        );
        CREATE TABLE candidate_sources (
            canonical_digest TEXT NOT NULL,
            source TEXT NOT NULL,
            first_seen_utc TEXT NOT NULL,
            last_seen_utc TEXT NOT NULL,
            claim_count INTEGER NOT NULL DEFAULT 0,
            PRIMARY KEY (canonical_digest, source)
        );
        INSERT INTO candidates VALUES (
            'legacy', 'old', '2026-01-01T00:00:00+00:00', '{}',
            'old', '2026-01-01T00:00:00+00:00', 1
        );
        INSERT INTO candidate_sources VALUES (
            'legacy', 'old', '2026-01-01T00:00:00+00:00',
            '2026-01-01T00:00:00+00:00', 1
        );
        """
    )
    connection.close()

    with CampaignDedup(path, owner_id="new") as dedup:
        assert dedup.get("legacy")["lifecycle_state"] == "completed"
        assert dedup.claim("legacy", source="new") is False
        assert dedup.stats()["schema_version"] == 2


@pytest.mark.parametrize(
    ("digest", "source"),
    [("", "shard"), ("digest", ""), ("   ", "shard"), ("digest", "   ")],
)
def test_claim_rejects_empty_keys(tmp_path, digest, source):
    with CampaignDedup(tmp_path / "campaign.sqlite3") as dedup:
        with pytest.raises(ValueError):
            dedup.claim(digest, source=source)
