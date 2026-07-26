"""Tests for durable cross-process campaign deduplication."""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from multiprocessing import get_context

import pytest

from evaluation.campaign_dedup import CampaignDedup


def _claim_in_process(payload: tuple[str, str]) -> bool:
    path, source = payload
    with CampaignDedup(path, busy_timeout_ms=10_000) as dedup:
        return dedup.claim(
            "a" * 64,
            source=source,
            metadata={"worker": source},
        )


def test_claim_preserves_first_provenance_and_tracks_sources(tmp_path):
    path = tmp_path / "campaign.sqlite3"
    with CampaignDedup(path) as dedup:
        assert dedup.claim(
            "digest-a",
            source="shard-00",
            metadata={"trial": 7},
        )
        assert not dedup.claim(
            "digest-a",
            source="shard-01",
            metadata={"trial": 99},
        )
        assert not dedup.claim("digest-a", source="shard-01")
        assert dedup.claim("digest-b", source="shard-01")

        record = dedup.get("digest-a")
        assert record is not None
        assert record["first_source"] == "shard-00"
        assert record["first_metadata"] == {"trial": 7}
        assert record["last_source"] == "shard-01"
        assert record["claim_count"] == 3

        assert [
            (row["source"], row["claim_count"])
            for row in dedup.sources("digest-a")
        ] == [("shard-00", 1), ("shard-01", 2)]
        assert dedup.stats() == {
            "schema_version": 1,
            "unique_candidates": 2,
            "total_claims": 4,
            "duplicate_claims": 2,
            "sources": [
                {
                    "source": "shard-00",
                    "unique_candidates": 1,
                    "total_claims": 1,
                },
                {
                    "source": "shard-01",
                    "unique_candidates": 2,
                    "total_claims": 3,
                },
            ],
        }

    with CampaignDedup(path) as reopened:
        assert reopened.get("digest-a")["claim_count"] == 3


def test_claim_is_atomic_across_processes(tmp_path):
    path = str(tmp_path / "concurrent.sqlite3")
    payloads = [(path, f"shard-{index % 4}") for index in range(32)]
    context = get_context("spawn")
    with ProcessPoolExecutor(
        max_workers=4,
        mp_context=context,
    ) as executor:
        first_claims = list(executor.map(_claim_in_process, payloads))

    assert sum(first_claims) == 1
    with CampaignDedup(path) as dedup:
        record = dedup.get("a" * 64)
        assert record is not None
        assert record["claim_count"] == len(payloads)
        assert sum(row["claim_count"] for row in dedup.sources("a" * 64)) == 32
        assert dedup.stats()["duplicate_claims"] == 31


@pytest.mark.parametrize(
    ("digest", "source"),
    [
        ("", "shard"),
        ("digest", ""),
        ("   ", "shard"),
        ("digest", "   "),
    ],
)
def test_claim_rejects_empty_keys(tmp_path, digest, source):
    with CampaignDedup(tmp_path / "campaign.sqlite3") as dedup:
        with pytest.raises(ValueError):
            dedup.claim(digest, source=source)
