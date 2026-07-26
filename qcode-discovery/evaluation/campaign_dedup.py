"""Durable cross-process structural deduplication for search campaigns.

Each search worker computes a canonical digest before starting an expensive
proof attempt and calls :meth:`CampaignDedup.claim`.  SQLite's unique primary
key makes that claim atomic across processes and shards.  The first worker
returns ``True``; all later workers return ``False`` while still contributing
source and duplicate-hit statistics.
"""

from __future__ import annotations

import json
import sqlite3
from collections.abc import Mapping
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
DEFAULT_BUSY_TIMEOUT_MS = 30_000


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="microseconds")


def _require_nonempty(value: str, *, name: str) -> str:
    normalized = str(value).strip()
    if not normalized:
        raise ValueError(f"{name} must be non-empty")
    return normalized


class CampaignDedup:
    """A small SQLite-backed registry of canonical structures.

    Instances are cheap and should be created independently in each process.
    The underlying database is configured in WAL mode, and every write waits
    up to ``busy_timeout_ms`` for a competing writer before failing.
    """

    def __init__(
        self,
        path: str | Path,
        *,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
    ) -> None:
        if int(busy_timeout_ms) <= 0:
            raise ValueError("busy_timeout_ms must be positive")

        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._connection = sqlite3.connect(
            self.path,
            timeout=int(busy_timeout_ms) / 1_000,
            isolation_level=None,
        )
        self._connection.row_factory = sqlite3.Row
        self._connection.execute(
            f"PRAGMA busy_timeout = {int(busy_timeout_ms)}",
        )
        self._connection.execute("PRAGMA journal_mode = WAL")
        self._connection.execute("PRAGMA synchronous = NORMAL")
        self._connection.execute("PRAGMA foreign_keys = ON")
        self._create_schema()

    def _create_schema(self) -> None:
        self._connection.executescript(
            """
            BEGIN IMMEDIATE;
            CREATE TABLE IF NOT EXISTS campaign_dedup_meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
            INSERT OR IGNORE INTO campaign_dedup_meta(key, value)
            VALUES ('schema_version', '1');

            CREATE TABLE IF NOT EXISTS candidates (
                canonical_digest TEXT PRIMARY KEY,
                first_source TEXT NOT NULL,
                first_seen_utc TEXT NOT NULL,
                first_metadata_json TEXT NOT NULL,
                last_source TEXT NOT NULL,
                last_seen_utc TEXT NOT NULL,
                claim_count INTEGER NOT NULL DEFAULT 0
                    CHECK (claim_count >= 0)
            );

            CREATE TABLE IF NOT EXISTS candidate_sources (
                canonical_digest TEXT NOT NULL,
                source TEXT NOT NULL,
                first_seen_utc TEXT NOT NULL,
                last_seen_utc TEXT NOT NULL,
                claim_count INTEGER NOT NULL DEFAULT 0
                    CHECK (claim_count >= 0),
                PRIMARY KEY (canonical_digest, source),
                FOREIGN KEY (canonical_digest)
                    REFERENCES candidates(canonical_digest)
                    ON DELETE CASCADE
            );
            CREATE INDEX IF NOT EXISTS candidate_sources_source_idx
            ON candidate_sources(source);
            COMMIT;
            """,
        )
        row = self._connection.execute(
            "SELECT value FROM campaign_dedup_meta WHERE key = 'schema_version'",
        ).fetchone()
        if row is None or int(row["value"]) != SCHEMA_VERSION:
            raise ValueError("unsupported campaign dedup schema version")

    def close(self) -> None:
        """Close this process's connection."""

        self._connection.close()

    def __enter__(self) -> CampaignDedup:
        return self

    def __exit__(self, exc_type, exc, traceback) -> None:
        self.close()

    def claim(
        self,
        canonical_digest: str,
        *,
        source: str,
        metadata: Mapping[str, Any] | None = None,
    ) -> bool:
        """Atomically claim a canonical digest.

        Returns ``True`` only for the first claim in the database.  Duplicate
        calls return ``False`` but update the aggregate counts and most recent
        source.  Metadata is stored only for the first claim so later shards
        cannot overwrite provenance.
        """

        digest = _require_nonempty(canonical_digest, name="canonical_digest")
        source_name = _require_nonempty(source, name="source")
        metadata_json = json.dumps(
            dict(metadata or {}),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        )
        now = _utc_now()

        self._connection.execute("BEGIN IMMEDIATE")
        try:
            cursor = self._connection.execute(
                """
                INSERT OR IGNORE INTO candidates(
                    canonical_digest,
                    first_source,
                    first_seen_utc,
                    first_metadata_json,
                    last_source,
                    last_seen_utc,
                    claim_count
                ) VALUES (?, ?, ?, ?, ?, ?, 0)
                """,
                (digest, source_name, now, metadata_json, source_name, now),
            )
            is_first = cursor.rowcount == 1
            self._connection.execute(
                """
                UPDATE candidates
                SET last_source = ?,
                    last_seen_utc = ?,
                    claim_count = claim_count + 1
                WHERE canonical_digest = ?
                """,
                (source_name, now, digest),
            )
            self._connection.execute(
                """
                INSERT INTO candidate_sources(
                    canonical_digest,
                    source,
                    first_seen_utc,
                    last_seen_utc,
                    claim_count
                ) VALUES (?, ?, ?, ?, 1)
                ON CONFLICT(canonical_digest, source) DO UPDATE SET
                    last_seen_utc = excluded.last_seen_utc,
                    claim_count = candidate_sources.claim_count + 1
                """,
                (digest, source_name, now, now),
            )
            self._connection.execute("COMMIT")
        except BaseException:
            self._connection.execute("ROLLBACK")
            raise
        return is_first

    def get(self, canonical_digest: str) -> dict[str, Any] | None:
        """Return the durable record for one digest, if present."""

        digest = _require_nonempty(canonical_digest, name="canonical_digest")
        row = self._connection.execute(
            """
            SELECT canonical_digest, first_source, first_seen_utc,
                   first_metadata_json, last_source, last_seen_utc, claim_count
            FROM candidates
            WHERE canonical_digest = ?
            """,
            (digest,),
        ).fetchone()
        if row is None:
            return None
        return {
            "canonical_digest": row["canonical_digest"],
            "first_source": row["first_source"],
            "first_seen_utc": row["first_seen_utc"],
            "first_metadata": json.loads(row["first_metadata_json"]),
            "last_source": row["last_source"],
            "last_seen_utc": row["last_seen_utc"],
            "claim_count": int(row["claim_count"]),
        }

    def sources(self, canonical_digest: str) -> list[dict[str, Any]]:
        """Return per-source claim counts for one digest."""

        digest = _require_nonempty(canonical_digest, name="canonical_digest")
        rows = self._connection.execute(
            """
            SELECT source, first_seen_utc, last_seen_utc, claim_count
            FROM candidate_sources
            WHERE canonical_digest = ?
            ORDER BY first_seen_utc, source
            """,
            (digest,),
        ).fetchall()
        return [
            {
                "source": row["source"],
                "first_seen_utc": row["first_seen_utc"],
                "last_seen_utc": row["last_seen_utc"],
                "claim_count": int(row["claim_count"]),
            }
            for row in rows
        ]

    def stats(self) -> dict[str, Any]:
        """Return campaign totals and a per-source breakdown."""

        totals = self._connection.execute(
            """
            SELECT COUNT(*) AS unique_candidates,
                   COALESCE(SUM(claim_count), 0) AS total_claims
            FROM candidates
            """,
        ).fetchone()
        source_rows = self._connection.execute(
            """
            SELECT source,
                   COUNT(*) AS unique_candidates,
                   SUM(claim_count) AS total_claims
            FROM candidate_sources
            GROUP BY source
            ORDER BY source
            """,
        ).fetchall()
        unique_candidates = int(totals["unique_candidates"])
        total_claims = int(totals["total_claims"])
        return {
            "schema_version": SCHEMA_VERSION,
            "unique_candidates": unique_candidates,
            "total_claims": total_claims,
            "duplicate_claims": total_claims - unique_candidates,
            "sources": [
                {
                    "source": row["source"],
                    "unique_candidates": int(row["unique_candidates"]),
                    "total_claims": int(row["total_claims"]),
                }
                for row in source_rows
            ],
        }
