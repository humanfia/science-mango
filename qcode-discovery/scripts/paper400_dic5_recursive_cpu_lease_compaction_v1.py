#!/usr/bin/env python3
"""Losslessly compact released recursive CPU leases out of the live catalog.

The frozen v1 catalog validator permits each CPU only once.  A safe lease
release followed by a later re-reservation therefore creates an otherwise
well-formed catalog that old v1 readers reject.  This sidecar fixes that
scheduler-metadata limitation without changing any split bundle, proof, or
certificate: it first preserves the complete signed original catalog in an
immutable archive receipt, then atomically publishes an equivalent live
catalog containing only currently RESERVED leases.

The action refuses duplicate active leases, unknown entry shapes, and any
unsealed catalog.  It is crash-recoverable: an archive includes the exact
post-compaction catalog, so a rerun can safely complete an interrupted atomic
publication.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
import time
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-cpu-lease-compaction-v1"
ARCHIVE_KIND = "paper400-dic5-recursive-cpu-lease-catalog-compaction-v1"
ARCHIVE_DIR = Path("cpu-lease-catalog-compaction-v1")


class CpuLeaseCompactionError(RuntimeError):
    """The live catalog is not eligible for lossless compaction."""


def _script_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "compaction_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
    }


def _read_catalog_tolerant(control: Path) -> dict[str, Any]:
    path = control / supervisor.CATALOG
    if not path.exists() or path.is_symlink():
        raise CpuLeaseCompactionError("CPU lease catalog is absent")
    value = supervisor._read_json(path)
    required = {"schema_version", "kind", "leases", "updated_at", "catalog_sha256"}
    if (
        set(value) != required
        or not recursive.selfhash_valid(value, "catalog_sha256")
        or value.get("schema_version") != supervisor.SCHEMA_VERSION
        or value.get("kind") != supervisor.CPU_CATALOG_KIND
        or type(value.get("leases")) is not list
        or type(value.get("updated_at")) not in {int, float}
    ):
        raise CpuLeaseCompactionError("CPU lease catalog envelope is malformed")
    active: set[int] = set()
    for entry in value["leases"]:
        if (
            type(entry) is not dict
            or set(entry) != {"cpu", "bundle", "reservation_sha256", "state", "created_at", "released_at"}
            or type(entry.get("cpu")) is not int
            or entry["cpu"] < 0
            or type(entry.get("bundle")) is not str
            or not recursive.is_sha256(entry.get("reservation_sha256"))
            or entry.get("state") not in {"RESERVED", "RELEASED"}
            or type(entry.get("created_at")) not in {int, float}
            or (entry.get("released_at") is not None and type(entry.get("released_at")) not in {int, float})
            or (entry.get("state") == "RESERVED" and entry.get("released_at") is not None)
            or (entry.get("state") == "RELEASED" and type(entry.get("released_at")) not in {int, float})
        ):
            raise CpuLeaseCompactionError("CPU lease catalog entry is malformed")
        if entry["state"] == "RESERVED":
            if entry["cpu"] in active:
                raise CpuLeaseCompactionError("CPU lease catalog has duplicate active reservations")
            active.add(entry["cpu"])
    return value


def _safe_archive_dir(control: Path) -> Path:
    target = control / ARCHIVE_DIR
    if target.exists() or target.is_symlink():
        return supervisor._safe_directory(target, require_mode_0700=True)
    try:
        os.mkdir(target, 0o700)
        supervisor._fsync_dir(control)
    except OSError as exc:
        raise CpuLeaseCompactionError("cannot create CPU lease archive directory") from exc
    return supervisor._safe_directory(target, require_mode_0700=True)


def _compacted_catalog(catalog: Mapping[str, Any], *, now: float) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": supervisor.SCHEMA_VERSION,
            "kind": supervisor.CPU_CATALOG_KIND,
            "leases": [dict(entry) for entry in catalog["leases"] if entry["state"] == "RESERVED"],
            "updated_at": now,
        },
        "catalog_sha256",
    )


def _archive_value(original: Mapping[str, Any], compacted: Mapping[str, Any]) -> dict[str, Any]:
    removed = [dict(entry) for entry in original["leases"] if entry["state"] == "RELEASED"]
    retained = [dict(entry) for entry in original["leases"] if entry["state"] == "RESERVED"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": ARCHIVE_KIND,
            "gate": GATE,
            "original_catalog_sha256": original["catalog_sha256"],
            "original_catalog": dict(original),
            "compacted_catalog_sha256": compacted["catalog_sha256"],
            "compacted_catalog": dict(compacted),
            "removed_released_leases": removed,
            "retained_reserved_leases": retained,
            "reason": "REMOVE_RELEASED_HISTORY_FROM_LIVE_UNIQUE_CPU_CATALOG",
            "source_binding": _script_binding(),
            "created_at": time.time(),
        },
        "record_sha256",
    )


def _validate_archive(value: Mapping[str, Any], *, original: Mapping[str, Any]) -> dict[str, Any]:
    required = {
        "schema_version", "kind", "gate", "original_catalog_sha256", "original_catalog",
        "compacted_catalog_sha256", "compacted_catalog", "removed_released_leases",
        "retained_reserved_leases", "reason", "source_binding", "created_at", "record_sha256",
    }
    if (
        set(value) != required
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != ARCHIVE_KIND
        or value.get("gate") != GATE
        or value.get("original_catalog_sha256") != original.get("catalog_sha256")
        or not supervisor._same(value.get("original_catalog"), original)
        or type(value.get("compacted_catalog")) is not dict
        or value.get("compacted_catalog_sha256") != value["compacted_catalog"].get("catalog_sha256")
        or not recursive.selfhash_valid(value["compacted_catalog"], "catalog_sha256")
    ):
        raise CpuLeaseCompactionError("CPU lease compaction archive is malformed")
    return dict(value)


def _archive_path(directory: Path, catalog_sha256: str) -> Path:
    return directory / f"000000-{catalog_sha256[:16]}.json"


def compact_released_cpu_leases(
    *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Archive released history and atomically restore v1-readable uniqueness."""

    control = supervisor._safe_directory(Path(control_root), require_mode_0700=True)
    with supervisor._catalog_lock(control):
        original = _read_catalog_tolerant(control)
        released = [entry for entry in original["leases"] if entry["state"] == "RELEASED"]
        if not released:
            # A strict v1 parse is an additional proof that the no-op catalog
            # remains usable by every existing v1 lifecycle.
            supervisor._load_catalog(control)
            return supervisor.seal(
                {
                    "schema_version": SCHEMA_VERSION,
                    "kind": ARCHIVE_KIND,
                    "gate": GATE,
                    "original_catalog_sha256": original["catalog_sha256"],
                    "compacted_catalog_sha256": original["catalog_sha256"],
                    "compacted": False,
                    "released_lease_count": 0,
                    "source_binding": _script_binding(),
                    "created_at": time.time(),
                },
                "record_sha256",
            )
        compacted = _compacted_catalog(original, now=time.time())
        directory = _safe_archive_dir(control)
        path = _archive_path(directory, original["catalog_sha256"])
        if path.exists() or path.is_symlink():
            archive = _validate_archive(supervisor._read_json(path), original=original)
            if not supervisor._same(archive["compacted_catalog"], compacted):
                # A crash-recovery archive keeps its original publication time;
                # use its exact sealed post-state rather than inventing another.
                compacted = dict(archive["compacted_catalog"])
        else:
            archive = _archive_value(original, compacted)
            supervisor._publish_json(path, archive)
        supervisor._atomic_rewrite(
            control / supervisor.CATALOG,
            supervisor.canonical_bytes(compacted) + b"\n",
        )
        # The frozen reader must accept the new active catalog before we report
        # success to a dispatcher waiting on these leases.
        supervisor._load_catalog(control)
        return supervisor.seal(
            {
                "schema_version": SCHEMA_VERSION,
                "kind": ARCHIVE_KIND,
                "gate": GATE,
                "original_catalog_sha256": original["catalog_sha256"],
                "compacted_catalog_sha256": compacted["catalog_sha256"],
                "archive_record_sha256": archive["record_sha256"],
                "archive_path": str(path),
                "compacted": True,
                "released_lease_count": len(released),
                "source_binding": _script_binding(),
                "created_at": time.time(),
            },
            "record_sha256",
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    sub.add_parser("compact", allow_abbrev=False)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action != "compact":  # pragma: no cover - argparse guards this
        raise CpuLeaseCompactionError("unsupported action")
    value = compact_released_cpu_leases(control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(value) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        CpuLeaseCompactionError,
        supervisor.RecursiveSplitSupervisorError,
        recursive.RecursiveSplitError,
        OSError,
        TypeError,
        ValueError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
