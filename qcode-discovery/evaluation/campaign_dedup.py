"""Lease-based cross-process structural deduplication for campaigns.

A claim is a renewable unit of work, not a permanent tombstone.  Crashed
workers leave an expiring lease that another process can reclaim.  Only
``complete`` turns the digest into a permanent duplicate.
"""

from __future__ import annotations

import json
import sqlite3
from collections.abc import Callable, Mapping
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any
from uuid import uuid4


SCHEMA_VERSION = 2
DEFAULT_BUSY_TIMEOUT_MS = 30_000
DEFAULT_LEASE_SECONDS = 900


def _format_utc(value: datetime) -> str:
    if value.tzinfo is None:
        raise ValueError("campaign dedup clock must be timezone-aware")
    return value.astimezone(timezone.utc).isoformat(timespec="microseconds")


def _require_nonempty(value: str, *, name: str) -> str:
    normalized = str(value).strip()
    if not normalized:
        raise ValueError(f"{name} must be non-empty")
    return normalized


class CampaignDedup:
    """SQLite registry with expiring ownership leases and permanent completion."""

    def __init__(
        self,
        path: str | Path,
        *,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
        lease_seconds: float = DEFAULT_LEASE_SECONDS,
        owner_id: str | None = None,
        clock: Callable[[], datetime] | None = None,
    ) -> None:
        if int(busy_timeout_ms) <= 0:
            raise ValueError("busy_timeout_ms must be positive")
        if float(lease_seconds) <= 0:
            raise ValueError("lease_seconds must be positive")
        self.path = Path(path)
        self.lease_seconds = float(lease_seconds)
        self.owner_id = _require_nonempty(owner_id or uuid4().hex, name="owner_id")
        self._clock = clock or (lambda: datetime.now(timezone.utc))
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._connection = sqlite3.connect(
            self.path,
            timeout=int(busy_timeout_ms) / 1_000,
            isolation_level=None,
        )
        self._connection.row_factory = sqlite3.Row
        self._connection.execute(f"PRAGMA busy_timeout = {int(busy_timeout_ms)}")
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
            VALUES ('schema_version', '2');

            CREATE TABLE IF NOT EXISTS candidates (
                canonical_digest TEXT PRIMARY KEY,
                first_source TEXT NOT NULL,
                first_seen_utc TEXT NOT NULL,
                first_metadata_json TEXT NOT NULL,
                last_source TEXT NOT NULL,
                last_seen_utc TEXT NOT NULL,
                claim_count INTEGER NOT NULL DEFAULT 0 CHECK (claim_count >= 0),
                lifecycle_state TEXT NOT NULL DEFAULT 'completed',
                lease_owner TEXT,
                lease_expires_utc TEXT,
                completed_utc TEXT
            );
            CREATE TABLE IF NOT EXISTS candidate_sources (
                canonical_digest TEXT NOT NULL,
                source TEXT NOT NULL,
                first_seen_utc TEXT NOT NULL,
                last_seen_utc TEXT NOT NULL,
                claim_count INTEGER NOT NULL DEFAULT 0 CHECK (claim_count >= 0),
                PRIMARY KEY (canonical_digest, source),
                FOREIGN KEY (canonical_digest)
                    REFERENCES candidates(canonical_digest) ON DELETE CASCADE
            );
            CREATE INDEX IF NOT EXISTS candidate_sources_source_idx
            ON candidate_sources(source);
            COMMIT;
            """
        )
        row = self._connection.execute(
            "SELECT value FROM campaign_dedup_meta WHERE key = 'schema_version'",
        ).fetchone()
        if row is None:
            raise ValueError("campaign dedup schema version is missing")
        version = int(row["value"])
        if version == 1:
            self._migrate_v1()
            version = SCHEMA_VERSION
        if version != SCHEMA_VERSION:
            raise ValueError("unsupported campaign dedup schema version")

    def _migrate_v1(self) -> None:
        """Migrate legacy permanent claims as completed records."""

        self._connection.execute("BEGIN IMMEDIATE")
        try:
            current = self._connection.execute(
                "SELECT value FROM campaign_dedup_meta WHERE key = 'schema_version'",
            ).fetchone()
            if current is None or int(current["value"]) != 1:
                self._connection.execute("COMMIT")
                return
            columns = {
                str(row["name"])
                for row in self._connection.execute(
                    "PRAGMA table_info(candidates)",
                ).fetchall()
            }
            additions = (
                ("lifecycle_state", "TEXT NOT NULL DEFAULT 'completed'"),
                ("lease_owner", "TEXT"),
                ("lease_expires_utc", "TEXT"),
                ("completed_utc", "TEXT"),
            )
            for name, declaration in additions:
                if name not in columns:
                    self._connection.execute(
                        f"ALTER TABLE candidates ADD COLUMN {name} {declaration}",
                    )
            self._connection.execute(
                """
                UPDATE candidates
                SET lifecycle_state = 'completed',
                    completed_utc = COALESCE(completed_utc, last_seen_utc),
                    lease_owner = NULL,
                    lease_expires_utc = NULL
                """
            )
            self._connection.execute(
                "UPDATE campaign_dedup_meta SET value = ? WHERE key = 'schema_version'",
                (str(SCHEMA_VERSION),),
            )
            self._connection.execute("COMMIT")
        except BaseException:
            self._connection.execute("ROLLBACK")
            raise

    def close(self) -> None:
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
        """Acquire a new or expired lease; completed digests stay unavailable."""

        digest = _require_nonempty(canonical_digest, name="canonical_digest")
        source_name = _require_nonempty(source, name="source")
        metadata_json = json.dumps(
            dict(metadata or {}), sort_keys=True, separators=(",", ":"),
            ensure_ascii=False,
        )
        now_value = self._clock()
        now = _format_utc(now_value)
        expires = _format_utc(now_value + timedelta(seconds=self.lease_seconds))
        self._connection.execute("BEGIN IMMEDIATE")
        try:
            cursor = self._connection.execute(
                """
                INSERT OR IGNORE INTO candidates(
                    canonical_digest, first_source, first_seen_utc,
                    first_metadata_json, last_source, last_seen_utc,
                    claim_count, lifecycle_state, lease_owner,
                    lease_expires_utc, completed_utc
                ) VALUES (?, ?, ?, ?, ?, ?, 0, 'leased', ?, ?, NULL)
                """,
                (
                    digest, source_name, now, metadata_json, source_name, now,
                    self.owner_id, expires,
                ),
            )
            acquired = cursor.rowcount == 1
            if not acquired:
                cursor = self._connection.execute(
                    """
                    UPDATE candidates
                    SET lifecycle_state = 'leased', lease_owner = ?,
                        lease_expires_utc = ?, completed_utc = NULL
                    WHERE canonical_digest = ?
                      AND lifecycle_state = 'leased'
                      AND (lease_owner = ?
                           OR COALESCE(lease_expires_utc, '') <= ?)
                    """,
                    (
                        self.owner_id, expires, digest,
                        self.owner_id, now,
                    ),
                )
                acquired = cursor.rowcount == 1
            self._connection.execute(
                """
                UPDATE candidates
                SET last_source = ?, last_seen_utc = ?,
                    claim_count = claim_count + 1
                WHERE canonical_digest = ?
                """,
                (source_name, now, digest),
            )
            self._connection.execute(
                """
                INSERT INTO candidate_sources(
                    canonical_digest, source, first_seen_utc,
                    last_seen_utc, claim_count
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
        return acquired

    def complete(self, canonical_digest: str) -> bool:
        """Permanently complete a digest iff this instance owns its lease."""

        digest = _require_nonempty(canonical_digest, name="canonical_digest")
        now = _format_utc(self._clock())
        self._connection.execute("BEGIN IMMEDIATE")
        try:
            cursor = self._connection.execute(
                """
                UPDATE candidates
                SET lifecycle_state = 'completed', completed_utc = ?,
                    lease_owner = NULL, lease_expires_utc = NULL,
                    last_seen_utc = ?
                WHERE canonical_digest = ?
                  AND lifecycle_state = 'leased'
                  AND lease_owner = ?
                """,
                (now, now, digest, self.owner_id),
            )
            completed = cursor.rowcount == 1
            self._connection.execute("COMMIT")
        except BaseException:
            self._connection.execute("ROLLBACK")
            raise
        return completed

    def get(self, canonical_digest: str) -> dict[str, Any] | None:
        digest = _require_nonempty(canonical_digest, name="canonical_digest")
        row = self._connection.execute(
            """
            SELECT canonical_digest, first_source, first_seen_utc,
                   first_metadata_json, last_source, last_seen_utc, claim_count,
                   lifecycle_state, lease_owner, lease_expires_utc, completed_utc
            FROM candidates WHERE canonical_digest = ?
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
            "lifecycle_state": row["lifecycle_state"],
            "lease_owner": row["lease_owner"],
            "lease_expires_utc": row["lease_expires_utc"],
            "completed_utc": row["completed_utc"],
        }

    def sources(self, canonical_digest: str) -> list[dict[str, Any]]:
        digest = _require_nonempty(canonical_digest, name="canonical_digest")
        rows = self._connection.execute(
            """
            SELECT source, first_seen_utc, last_seen_utc, claim_count
            FROM candidate_sources WHERE canonical_digest = ?
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
        totals = self._connection.execute(
            """
            SELECT COUNT(*) AS unique_candidates,
                   COALESCE(SUM(claim_count), 0) AS total_claims,
                   SUM(lifecycle_state = 'leased') AS leased_candidates,
                   SUM(lifecycle_state = 'completed') AS completed_candidates
            FROM candidates
            """
        ).fetchone()
        source_rows = self._connection.execute(
            """
            SELECT source, COUNT(*) AS unique_candidates,
                   SUM(claim_count) AS total_claims
            FROM candidate_sources GROUP BY source ORDER BY source
            """
        ).fetchall()
        unique_candidates = int(totals["unique_candidates"])
        total_claims = int(totals["total_claims"])
        return {
            "schema_version": SCHEMA_VERSION,
            "unique_candidates": unique_candidates,
            "total_claims": total_claims,
            "duplicate_claims": total_claims - unique_candidates,
            "leased_candidates": int(totals["leased_candidates"] or 0),
            "completed_candidates": int(totals["completed_candidates"] or 0),
            "sources": [
                {
                    "source": row["source"],
                    "unique_candidates": int(row["unique_candidates"]),
                    "total_claims": int(row["total_claims"]),
                }
                for row in source_rows
            ],
        }
