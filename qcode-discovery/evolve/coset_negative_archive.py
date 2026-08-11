"""Verified negative-mechanism archive for the coset Stage-1 search.

Only independently replayed logical-operator witnesses may enter this file.
The archive is advisory search state: it may reduce evolutionary fitness, but
it is never positive distance evidence and is never consumed by certification.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import math
import os
import stat
import uuid
from collections.abc import Iterable, Mapping, Sequence
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import numpy as np

from evaluation.construction import (
    build_css_code_from_claim,
    construction_source_fingerprint,
)
from evaluation.certificate import (
    FORMULATION as CSS_EXACT_FORMULATION,
    THRESHOLD_FORMULATION as CSS_THRESHOLD_FORMULATION,
    pack_vector,
    verify_css_witness,
    verify_direction_evidence,
)
from evaluation.coset_action_catalog import (
    V2_CATALOG_ID,
    action_catalog_identity,
)
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_FORMULATION,
    verify_css_threshold_sat_witness,
)
from evaluation.final_gate import minimum_winning_distance
from evaluation.low_weight_oracle import verify_css_low_weight_oracle
from evaluation.structural_dedup import (
    canonical_digest as structural_canonical_digest,
    structural_screen_runtime_fingerprint,
)
from evaluation.target_policy import (
    DEFAULT_TARGET_MODE,
    TARGET_MODE_GIST,
    minimum_target_distance,
    validate_target_binding,
    validate_target_mode,
)
from evaluation.coset_two_block import normalize_coset_two_block_construction
from evaluation.two_block_sparse_kernel_oracle import (
    verify_two_block_sparse_kernel_oracle,
)
from evolve.coset_search_contract import (
    COSET_CANDIDATE_SCHEMA_VERSION,
    COSET_CANDIDATE_SCHEMA_VERSION_V3,
    COSET_RENDERER_V3_ID,
    COSET_REPRESENTATION_ID,
    COSET_REPRESENTATION_ID_V3,
    action_search_view,
    coset_candidate_digest,
    normalize_coset_candidate,
    trusted_coset_renderer_registry_document,
)
from scripts.screen_frontier_sat import verify_construction_symmetry


NEGATIVE_ARCHIVE_PATH_ENV = "QCODE_COSET_NEGATIVE_ARCHIVE_PATH"
NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV = (
    "QCODE_COSET_NEGATIVE_ARCHIVE_SNAPSHOT_PATH"
)
NEGATIVE_FEEDBACK_SNAPSHOT_KIND = "qcode-coset-negative-feedback-snapshot-v1"
NEGATIVE_FEEDBACK_SNAPSHOT_SCHEMA_VERSION = 1
STAGE3_NEGATIVE_INPUTS_ENV = "QCODE_COSET_STAGE3_NEGATIVE_INPUTS"
STAGE2_NEGATIVE_INPUTS_ENV = "QCODE_COSET_STAGE2_NEGATIVE_INPUTS"
FRONTIER_NEGATIVE_INPUTS_ENV = "QCODE_COSET_FRONTIER_NEGATIVE_INPUTS"
NEGATIVE_ARCHIVE_KIND = "qcode-coset-verified-negative-mechanisms"
NEGATIVE_ARCHIVE_SCHEMA_VERSION = 1
NEGATIVE_EVENT_KIND = "qcode-coset-verified-negative-event"
NEGATIVE_EVENT_SCHEMA_VERSION = 1
NEGATIVE_MOTIF_KIND = "qcode-coset-negative-mechanism-motif"
NEGATIVE_MOTIF_SCHEMA_VERSION = 1
STAGE3_GATE = "qldpc-frontier-sat-sector-exact-screen"
STAGE3_SCHEMA_VERSION = 1
FRONTIER_GATE = "qldpc-frontier-threshold-screen"
FRONTIER_SCHEMA_VERSION = 2
_MAX_ARCHIVE_BYTES = 256 * 1024 * 1024
_MAX_STAGE3_BYTES = 512 * 1024 * 1024
_MAX_ARCHIVE_EVENTS = 250_000
_MAX_WITNESS_ORBIT_STATES = 8_192
_EXPECTED_UNSET = object()


class NegativeArchiveError(ValueError):
    """Raised when archive state or proposed evidence fails closed."""


def _canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise NegativeArchiveError("value is not strict JSON") from exc


def _sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _file_sha256(path: Path) -> str:
    if path.is_symlink() or not path.is_file():
        raise NegativeArchiveError(f"source binding is not a regular file: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _is_finite_number(value: Any) -> bool:
    return type(value) in {int, float} and math.isfinite(float(value))


_PROJECT = Path(__file__).resolve().parent.parent


def _source_binding() -> dict[str, Any]:
    catalog = action_catalog_identity(V2_CATALOG_ID)
    renderer_registry = trusted_coset_renderer_registry_document()
    sources = {
        "coset_negative_archive.py": _file_sha256(Path(__file__).resolve()),
        "coset_search_contract.py": _file_sha256(
            _PROJECT / "evolve" / "coset_search_contract.py"
        ),
        "low_weight_oracle.py": _file_sha256(
            _PROJECT / "evaluation" / "low_weight_oracle.py"
        ),
        "distance_sat.py": _file_sha256(
            _PROJECT / "evaluation" / "distance_sat.py"
        ),
        "distance_milp.py": _file_sha256(
            _PROJECT / "evaluation" / "distance_milp.py"
        ),
        "structural_dedup.py": _file_sha256(
            _PROJECT / "evaluation" / "structural_dedup.py"
        ),
        "tanner_equivalence.py": _file_sha256(
            _PROJECT / "evaluation" / "tanner_equivalence.py"
        ),
        "certificate.py": _file_sha256(
            _PROJECT / "evaluation" / "certificate.py"
        ),
        "target_policy.py": _file_sha256(
            _PROJECT / "evaluation" / "target_policy.py"
        ),
        "two_block_sparse_kernel_oracle.py": _file_sha256(
            _PROJECT / "evaluation" / "two_block_sparse_kernel_oracle.py"
        ),
        # Stage-2 global SAT negatives are replayed from the producer's
        # self-hashed compact cache.  Bind the archive to the exact producer
        # implementation whose candidate/cache binding we recompute below.
        "audit_candidate_pool.py": _file_sha256(
            _PROJECT / "scripts" / "audit_candidate_pool.py"
        ),
        "screen_frontier_sat.py": _file_sha256(
            _PROJECT / "scripts" / "screen_frontier_sat.py"
        ),
        "screen_frontier_candidate.py": _file_sha256(
            _PROJECT / "scripts" / "screen_frontier_candidate.py"
        ),
    }
    structural_runtime = structural_screen_runtime_fingerprint()
    binding = {
        "renderer_registry": renderer_registry,
        "action_catalog": catalog,
        "construction_source_fingerprint": construction_source_fingerprint(),
        "structural_runtime": structural_runtime,
        "verifier_sources": sources,
    }
    return {**binding, "binding_sha256": _sha256(binding)}


# Freeze the identity of the code actually imported into this process.  This
# avoids silently rebinding an already-loaded verifier if a source file is
# edited concurrently during a development run.
_BOUND_SOURCE = _source_binding()


def resolve_archive_path(
    candidate_log_path: str | Path | None = None,
) -> Path | None:
    """Resolve an absolute archive path, or ``None`` when persistence is off."""

    explicit = os.environ.get(NEGATIVE_ARCHIVE_PATH_ENV)
    if explicit:
        path = Path(explicit).expanduser()
    else:
        raw_log = candidate_log_path or os.environ.get("QCODE_CANDIDATE_LOG_PATH")
        if not raw_log:
            return None
        log_path = Path(raw_log).expanduser()
        if not log_path.is_absolute():
            raise NegativeArchiveError("coset candidate log path must be absolute")
        version = str(_BOUND_SOURCE["binding_sha256"])[:16]
        path = log_path.parent / f".coset-negative-mechanisms-v1-{version}.json"
    if not path.is_absolute():
        raise NegativeArchiveError("coset negative archive path must be absolute")
    return path


def resolve_snapshot_path(
    live_archive_path: Path | str | None = None,
) -> Path | None:
    """Resolve the immutable read side for one negative-feedback epoch.

    Historical and unmanaged launches intentionally fall back to the live
    archive. Managed Humanize slices always set the snapshot environment
    variable to a sealed, round-local file.
    """

    explicit = os.environ.get(NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV)
    if explicit:
        path = Path(explicit).expanduser()
    elif live_archive_path is not None:
        path = Path(live_archive_path).expanduser()
    else:
        path = resolve_archive_path()
    if path is None:
        return None
    if not path.is_absolute():
        raise NegativeArchiveError(
            "coset negative archive snapshot path must be absolute"
        )
    return path


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise NegativeArchiveError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> Any:
    raise NegativeArchiveError(f"non-finite JSON number: {value}")


def _read_regular_bytes(path: Path, *, limit: int) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except FileNotFoundError:
        raise
    except OSError as exc:
        raise NegativeArchiveError(f"cannot safely open {path}: {exc}") from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise NegativeArchiveError(f"path is not a regular file: {path}")
        if metadata.st_size > limit:
            raise NegativeArchiveError(f"JSON file exceeds size limit: {path}")
        chunks: list[bytes] = []
        remaining = limit + 1
        while remaining:
            chunk = os.read(descriptor, min(1024 * 1024, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        if len(payload) > limit:
            raise NegativeArchiveError(f"JSON file exceeds size limit: {path}")
        return payload
    finally:
        os.close(descriptor)


def _strict_json_bytes(payload: bytes, *, where: str) -> dict[str, Any]:
    try:
        value = json.loads(
            payload.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_constant,
        )
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise NegativeArchiveError(f"{where} is not strict JSON") from exc
    if not isinstance(value, dict):
        raise NegativeArchiveError(f"{where} must contain one JSON object")
    _canonical_bytes(value)
    return value


def _empty_archive() -> dict[str, Any]:
    value: dict[str, Any] = {
        "schema_version": NEGATIVE_ARCHIVE_SCHEMA_VERSION,
        "kind": NEGATIVE_ARCHIVE_KIND,
        "binding": dict(_BOUND_SOURCE),
        "events": {},
        "motifs": {},
        "coordinate_aggregates": {},
    }
    value["archive_sha256"] = _sha256(value)
    return value


def _validate_sealed_record(
    value: Mapping[str, Any],
    *,
    hash_field: str,
    where: str,
) -> None:
    unsigned = dict(value)
    digest = unsigned.pop(hash_field, None)
    if not _is_sha256(digest) or digest != _sha256(unsigned):
        raise NegativeArchiveError(f"{where} self-hash mismatch")


def _validate_archive(value: Mapping[str, Any]) -> dict[str, Any]:
    if set(value) != {
        "schema_version", "kind", "binding", "events", "motifs",
        "coordinate_aggregates",
        "archive_sha256",
    }:
        raise NegativeArchiveError("negative archive envelope fields changed")
    _validate_sealed_record(value, hash_field="archive_sha256", where="archive")
    if (
        value.get("schema_version") != NEGATIVE_ARCHIVE_SCHEMA_VERSION
        or value.get("kind") != NEGATIVE_ARCHIVE_KIND
        or value.get("binding") != _BOUND_SOURCE
    ):
        raise NegativeArchiveError("negative archive source/representation binding mismatch")
    events = value.get("events")
    motifs = value.get("motifs")
    coordinate_aggregates = value.get("coordinate_aggregates")
    if (
        not isinstance(events, Mapping)
        or not isinstance(motifs, Mapping)
        or not isinstance(coordinate_aggregates, Mapping)
    ):
        raise NegativeArchiveError("negative archive indexes are invalid")
    if len(events) > _MAX_ARCHIVE_EVENTS:
        raise NegativeArchiveError("negative archive event limit exceeded")
    motif_to_events: dict[str, list[str]] = {}
    for event_sha, raw in events.items():
        if not _is_sha256(event_sha) or not isinstance(raw, Mapping):
            raise NegativeArchiveError("negative archive event index is invalid")
        if raw.get("event_sha256") != event_sha:
            raise NegativeArchiveError("negative archive event index/hash mismatch")
        _validate_sealed_record(raw, hash_field="event_sha256", where="event")
        if (
            raw.get("schema_version") != NEGATIVE_EVENT_SCHEMA_VERSION
            or raw.get("kind") != NEGATIVE_EVENT_KIND
            or not isinstance(raw.get("motif"), Mapping)
        ):
            raise NegativeArchiveError("negative archive event schema is invalid")
        motif_sha = raw["motif"].get("motif_sha256")
        if not _is_sha256(motif_sha):
            raise NegativeArchiveError("negative archive event motif hash is invalid")
        _validate_sealed_record(
            raw["motif"], hash_field="motif_sha256", where="motif"
        )
        motif_to_events.setdefault(str(motif_sha), []).append(str(event_sha))
    if set(motifs) != set(motif_to_events):
        raise NegativeArchiveError("negative archive motif index is incomplete")
    for motif_sha, raw in motifs.items():
        if not isinstance(raw, Mapping) or set(raw) != {
            "motif", "event_sha256s", "event_count",
        }:
            raise NegativeArchiveError("negative archive motif aggregate is invalid")
        expected = sorted(motif_to_events[motif_sha])
        if (
            raw.get("motif")
            != events[expected[0]]["motif"]
            or raw.get("event_sha256s") != expected
            or raw.get("event_count") != len(expected)
        ):
            raise NegativeArchiveError("negative archive motif aggregate mismatch")
    coordinate_events: dict[str, list[str]] = {}
    coordinate_motifs: dict[str, set[str]] = {}
    coordinate_values: dict[str, Mapping[str, Any]] = {}
    for event_sha, event in events.items():
        motif = event["motif"]
        motif_sha = str(motif["motif_sha256"])
        coordinates = motif.get("coordinates")
        if not isinstance(coordinates, Mapping):
            raise NegativeArchiveError("negative motif coordinates are missing")
        for coordinate in coordinates.values():
            if not isinstance(coordinate, Mapping):
                raise NegativeArchiveError("negative motif coordinate is invalid")
            key = coordinate.get("key_sha256")
            if not _is_sha256(key):
                raise NegativeArchiveError("negative motif coordinate key is invalid")
            existing = coordinate_values.setdefault(str(key), coordinate)
            if existing != coordinate:
                raise NegativeArchiveError("negative motif coordinate hash collision")
            coordinate_events.setdefault(str(key), []).append(str(event_sha))
            coordinate_motifs.setdefault(str(key), set()).add(motif_sha)
    if set(coordinate_aggregates) != set(coordinate_events):
        raise NegativeArchiveError("negative archive coordinate index is incomplete")
    for key, aggregate in coordinate_aggregates.items():
        expected_events = sorted(coordinate_events[key])
        expected_motifs = sorted(coordinate_motifs[key])
        if (
            not isinstance(aggregate, Mapping)
            or aggregate.get("coordinate") != coordinate_values[key]
            or aggregate.get("event_sha256s") != expected_events
            or aggregate.get("motif_sha256s") != expected_motifs
            or aggregate.get("event_count") != len(expected_events)
            or aggregate.get("motif_count") != len(expected_motifs)
        ):
            raise NegativeArchiveError("negative archive coordinate aggregate mismatch")
    return dict(value)


def load_archive(path: Path | str | None) -> dict[str, Any]:
    if path is None:
        return _empty_archive()
    selected = Path(path)
    try:
        payload = _read_regular_bytes(selected, limit=_MAX_ARCHIVE_BYTES)
    except FileNotFoundError:
        return _empty_archive()
    return _validate_archive(_strict_json_bytes(payload, where=str(selected)))


@contextmanager
def _archive_lock(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = path.with_name(path.name + ".lock")
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(lock_path, flags, 0o600)
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise NegativeArchiveError("negative archive lock is not regular")
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def _atomic_write(path: Path, value: Mapping[str, Any]) -> None:
    encoded = _canonical_bytes(value) + b"\n"
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        offset = 0
        while offset < len(encoded):
            count = os.write(descriptor, encoded[offset:])
            if count <= 0:
                raise OSError("negative archive write made no progress")
            offset += count
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    try:
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_CLOEXEC)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _immutable_file_identity(path: Path, *, limit: int) -> dict[str, Any]:
    payload = _read_regular_bytes(path, limit=limit)
    return {
        "path": str(path.resolve(strict=True)),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }


def _write_immutable_json(path: Path, value: Mapping[str, Any]) -> None:
    """Atomically publish one durable read-only JSON file without replacement."""

    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = _canonical_bytes(value) + b"\n"
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(temporary, flags, 0o400)
        try:
            offset = 0
            while offset < len(encoded):
                count = os.write(descriptor, encoded[offset:])
                if count <= 0:
                    raise OSError(
                        "negative archive snapshot write made no progress"
                    )
                offset += count
            os.fsync(descriptor)
            os.fchmod(descriptor, 0o400)
        finally:
            os.close(descriptor)
        # A hard link is the portable no-clobber publication primitive here:
        # the final name appears only after the complete inode is durable, and
        # a racing/crash-recovered publisher can never replace it.
        try:
            os.link(temporary, path, follow_symlinks=False)
        except FileExistsError:
            pass
        directory = os.open(path.parent, os.O_RDONLY | os.O_CLOEXEC)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def load_feedback_snapshot_manifest(
    manifest_path: Path | str,
    *,
    expected_live_archive_path: Path | str | None = None,
    expected_snapshot_path: Path | str | None = None,
    expected_feedback_epoch: int | None = None,
    expected_run_id: str | None = None,
    expected_round_number: int | None = None,
    expected_parent_snapshot_sha256: object = _EXPECTED_UNSET,
) -> dict[str, Any]:
    """Validate a sealed snapshot and its source-bound archive payload."""

    selected = Path(manifest_path).expanduser()
    if not selected.is_absolute():
        raise NegativeArchiveError("negative feedback manifest path must be absolute")
    manifest = _strict_json_bytes(
        _read_regular_bytes(selected, limit=1024 * 1024),
        where=str(selected),
    )
    expected_fields = {
        "schema_version",
        "kind",
        "run_id",
        "round",
        "feedback_epoch",
        "live_archive_path",
        "source_archive_sha256",
        "archive_sha256",
        "archive_binding_sha256",
        "snapshot_path",
        "snapshot_sha256",
        "snapshot_bytes",
        "parent_snapshot_sha256",
        "materialized_at",
        "manifest_sha256",
    }
    if set(manifest) != expected_fields:
        raise NegativeArchiveError("negative feedback manifest fields changed")
    _validate_sealed_record(
        manifest,
        hash_field="manifest_sha256",
        where="negative feedback manifest",
    )
    live_path = Path(str(manifest.get("live_archive_path", ""))).expanduser()
    snapshot_path = Path(str(manifest.get("snapshot_path", ""))).expanduser()
    if (
        manifest.get("schema_version")
        != NEGATIVE_FEEDBACK_SNAPSHOT_SCHEMA_VERSION
        or manifest.get("kind") != NEGATIVE_FEEDBACK_SNAPSHOT_KIND
        or not isinstance(manifest.get("run_id"), str)
        or not manifest["run_id"]
        or isinstance(manifest.get("round"), bool)
        or not isinstance(manifest.get("round"), int)
        or manifest["round"] < 1
        or isinstance(manifest.get("feedback_epoch"), bool)
        or not isinstance(manifest.get("feedback_epoch"), int)
        or manifest["feedback_epoch"] < 1
        or not live_path.is_absolute()
        or not snapshot_path.is_absolute()
        or live_path == snapshot_path
        or not isinstance(manifest.get("materialized_at"), str)
        or not manifest["materialized_at"]
    ):
        raise NegativeArchiveError("negative feedback manifest identity is invalid")
    if expected_live_archive_path is not None and live_path != Path(
        expected_live_archive_path
    ).expanduser():
        raise NegativeArchiveError("negative feedback live archive path changed")
    if expected_snapshot_path is not None and snapshot_path != Path(
        expected_snapshot_path
    ).expanduser():
        raise NegativeArchiveError("negative feedback snapshot path changed")
    if (
        expected_feedback_epoch is not None
        and manifest["feedback_epoch"] != expected_feedback_epoch
    ):
        raise NegativeArchiveError("negative feedback epoch changed")
    if expected_run_id is not None and manifest["run_id"] != expected_run_id:
        raise NegativeArchiveError("negative feedback run_id changed")
    if (
        expected_round_number is not None
        and manifest["round"] != expected_round_number
    ):
        raise NegativeArchiveError("negative feedback round changed")
    if (
        expected_parent_snapshot_sha256 is not _EXPECTED_UNSET
        and manifest["parent_snapshot_sha256"]
        != expected_parent_snapshot_sha256
    ):
        raise NegativeArchiveError("negative feedback parent snapshot changed")
    hashes = (
        manifest.get("source_archive_sha256"),
        manifest.get("archive_sha256"),
        manifest.get("archive_binding_sha256"),
        manifest.get("snapshot_sha256"),
    )
    parent_sha = manifest.get("parent_snapshot_sha256")
    if any(not _is_sha256(value) for value in hashes) or (
        parent_sha is not None and not _is_sha256(parent_sha)
    ):
        raise NegativeArchiveError("negative feedback manifest hashes are invalid")
    identity = _immutable_file_identity(snapshot_path, limit=_MAX_ARCHIVE_BYTES)
    if (
        identity["sha256"] != manifest["snapshot_sha256"]
        or identity["bytes"] != manifest["snapshot_bytes"]
    ):
        raise NegativeArchiveError("negative feedback snapshot file changed")
    archive = load_archive(snapshot_path)
    if (
        archive.get("archive_sha256") != manifest["archive_sha256"]
        or manifest["source_archive_sha256"] != manifest["archive_sha256"]
        or archive.get("binding", {}).get("binding_sha256")
        != manifest["archive_binding_sha256"]
    ):
        raise NegativeArchiveError("negative feedback snapshot archive binding changed")
    return dict(manifest)


def materialize_feedback_snapshot(
    live_archive_path: Path | str,
    snapshot_path: Path | str,
    manifest_path: Path | str,
    *,
    run_id: str,
    round_number: int,
    feedback_epoch: int,
    parent_snapshot_sha256: str | None = None,
) -> dict[str, Any]:
    """Freeze one live-archive epoch into no-overwrite snapshot artifacts.

    An orphan snapshot is deliberately adopted after validation. This closes
    the crash window between snapshot creation and manifest publication: a
    retry cannot silently take a newer view of the mutable live archive.
    """

    live = Path(live_archive_path).expanduser()
    snapshot = Path(snapshot_path).expanduser()
    manifest_file = Path(manifest_path).expanduser()
    if not all(path.is_absolute() for path in (live, snapshot, manifest_file)):
        raise NegativeArchiveError("negative feedback paths must be absolute")
    if len({live, snapshot, manifest_file}) != 3:
        raise NegativeArchiveError("negative feedback paths must be distinct")
    if not isinstance(run_id, str) or not run_id:
        raise NegativeArchiveError("negative feedback run_id is invalid")
    if (
        isinstance(round_number, bool)
        or not isinstance(round_number, int)
        or round_number < 1
        or isinstance(feedback_epoch, bool)
        or not isinstance(feedback_epoch, int)
        or feedback_epoch < 1
        or (parent_snapshot_sha256 is not None and not _is_sha256(parent_snapshot_sha256))
    ):
        raise NegativeArchiveError("negative feedback epoch identity is invalid")
    if manifest_file.exists() or manifest_file.is_symlink():
        return load_feedback_snapshot_manifest(
            manifest_file,
            expected_live_archive_path=live,
            expected_snapshot_path=snapshot,
            expected_feedback_epoch=feedback_epoch,
            expected_run_id=run_id,
            expected_round_number=round_number,
            expected_parent_snapshot_sha256=parent_snapshot_sha256,
        )

    if snapshot.exists() or snapshot.is_symlink():
        archive = load_archive(snapshot)
    else:
        with _archive_lock(live):
            archive = load_archive(live)
            _write_immutable_json(snapshot, archive)
        # A concurrent no-clobber publisher may have won. Always bind the
        # actually published, independently source-validated archive.
        archive = load_archive(snapshot)
    try:
        os.chmod(snapshot, 0o400, follow_symlinks=False)
    except (NotImplementedError, OSError) as exc:
        raise NegativeArchiveError(
            "cannot make negative feedback snapshot read-only"
        ) from exc
    snapshot_identity = _immutable_file_identity(
        snapshot, limit=_MAX_ARCHIVE_BYTES
    )
    payload: dict[str, Any] = {
        "schema_version": NEGATIVE_FEEDBACK_SNAPSHOT_SCHEMA_VERSION,
        "kind": NEGATIVE_FEEDBACK_SNAPSHOT_KIND,
        "run_id": run_id,
        "round": round_number,
        "feedback_epoch": feedback_epoch,
        "live_archive_path": str(live),
        "source_archive_sha256": archive["archive_sha256"],
        "archive_sha256": archive["archive_sha256"],
        "archive_binding_sha256": archive["binding"]["binding_sha256"],
        "snapshot_path": snapshot_identity["path"],
        "snapshot_sha256": snapshot_identity["sha256"],
        "snapshot_bytes": snapshot_identity["bytes"],
        "parent_snapshot_sha256": parent_snapshot_sha256,
        "materialized_at": datetime.now(timezone.utc).isoformat(),
    }
    payload["manifest_sha256"] = _sha256(payload)
    _write_immutable_json(manifest_file, payload)
    return load_feedback_snapshot_manifest(
        manifest_file,
        expected_live_archive_path=live,
        expected_snapshot_path=snapshot,
        expected_feedback_epoch=feedback_epoch,
        expected_run_id=run_id,
        expected_round_number=round_number,
        expected_parent_snapshot_sha256=parent_snapshot_sha256,
    )


def _archive_summary(value: Mapping[str, Any], *, added: int = 0) -> dict[str, Any]:
    events = value["events"]
    motifs = value["motifs"]
    sources: dict[str, int] = {}
    for event in events.values():
        name = str(event["proof"]["source"])
        sources[name] = sources.get(name, 0) + 1
    return {
        "enabled": True,
        "binding_sha256": _BOUND_SOURCE["binding_sha256"],
        "event_count": len(events),
        "motif_count": len(motifs),
        "coordinate_count": len(value["coordinate_aggregates"]),
        "events_added": int(added),
        "source_counts": dict(sorted(sources.items())),
    }


def _merge_events(path: Path | None, events: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    if path is None:
        return {
            "enabled": False,
            "binding_sha256": _BOUND_SOURCE["binding_sha256"],
            "event_count": 0,
            "motif_count": 0,
            "coordinate_count": 0,
            "events_added": 0,
            "source_counts": {},
        }
    with _archive_lock(path):
        archive = load_archive(path)
        indexed = dict(archive["events"])
        added = 0
        for raw in events:
            event = dict(raw)
            event_sha = event.get("event_sha256")
            if not _is_sha256(event_sha):
                raise NegativeArchiveError("proposed negative event is unsealed")
            _validate_sealed_record(event, hash_field="event_sha256", where="event")
            existing = indexed.get(event_sha)
            if existing is not None:
                if existing != event:
                    raise NegativeArchiveError("negative event hash collision")
                continue
            if len(indexed) >= _MAX_ARCHIVE_EVENTS:
                raise NegativeArchiveError("negative archive event limit exceeded")
            indexed[str(event_sha)] = event
            added += 1
        if added:
            motif_events: dict[str, list[str]] = {}
            for event_sha, event in indexed.items():
                motif_sha = str(event["motif"]["motif_sha256"])
                motif_events.setdefault(motif_sha, []).append(event_sha)
            motif_index = {}
            for motif_sha, event_shas in motif_events.items():
                ordered = sorted(event_shas)
                motif_index[motif_sha] = {
                    "motif": indexed[ordered[0]]["motif"],
                    "event_sha256s": ordered,
                    "event_count": len(ordered),
                }
            coordinate_index: dict[str, dict[str, Any]] = {}
            for event_sha, event in indexed.items():
                motif = event["motif"]
                motif_sha = str(motif["motif_sha256"])
                for coordinate in motif["coordinates"].values():
                    key = str(coordinate["key_sha256"])
                    aggregate = coordinate_index.setdefault(key, {
                        "coordinate": coordinate,
                        "event_sha256s": [],
                        "motif_sha256s": [],
                    })
                    if aggregate["coordinate"] != coordinate:
                        raise NegativeArchiveError("negative coordinate hash collision")
                    aggregate["event_sha256s"].append(event_sha)
                    aggregate["motif_sha256s"].append(motif_sha)
            for aggregate in coordinate_index.values():
                aggregate["event_sha256s"] = sorted(set(
                    aggregate["event_sha256s"]
                ))
                aggregate["motif_sha256s"] = sorted(set(
                    aggregate["motif_sha256s"]
                ))
                aggregate["event_count"] = len(aggregate["event_sha256s"])
                aggregate["motif_count"] = len(aggregate["motif_sha256s"])
            archive = {
                "schema_version": NEGATIVE_ARCHIVE_SCHEMA_VERSION,
                "kind": NEGATIVE_ARCHIVE_KIND,
                "binding": dict(_BOUND_SOURCE),
                "events": dict(sorted(indexed.items())),
                "motifs": dict(sorted(motif_index.items())),
                "coordinate_aggregates": dict(sorted(coordinate_index.items())),
            }
            archive["archive_sha256"] = _sha256(archive)
            _validate_archive(archive)
            _atomic_write(path, archive)
        return _archive_summary(archive, added=added)


def _expected_construction(candidate: Mapping[str, Any]) -> dict[str, Any]:
    normalized = normalize_coset_candidate(candidate)
    catalog = action_catalog_identity(V2_CATALOG_ID)
    return {
        "kind": "coset-two-block-v2",
        # Renderer v2 and v3 both compile to the same immutable construction
        # adapter.  The renderer identity remains in the Stage-1 candidate;
        # it must never be confused with this builder representation.
        "representation_id": COSET_REPRESENTATION_ID,
        "action_id": normalized["action_id"],
        "action_catalog_id": V2_CATALOG_ID,
        "action_catalog_sha256": catalog["sha256"],
        "left_support": list(normalized["left_support"]),
        "right_support": list(normalized["right_support"]),
    }


def _build_construction(construction: Mapping[str, Any]) -> dict[str, Any]:
    try:
        canonical = normalize_coset_two_block_construction(construction)
    except (KeyError, TypeError, ValueError) as exc:
        raise NegativeArchiveError("coset construction is invalid") from exc
    if canonical != dict(construction):
        raise NegativeArchiveError("coset construction is not canonical")
    if (
        canonical.get("kind") != "coset-two-block-v2"
        or canonical.get("representation_id") != COSET_REPRESENTATION_ID
        or canonical.get("action_catalog_id") != V2_CATALOG_ID
    ):
        raise NegativeArchiveError("construction is not the registered v2 adapter")
    code = build_css_code_from_claim({"construction": canonical})
    hx, hz, lx, lz = (
        np.asarray(matrix, dtype=np.uint8) & 1
        for matrix in get_code_matrices(code)
    )
    view = action_search_view(str(canonical["action_id"]))
    n = int(hx.shape[1])
    k = int(code.dimension)
    if n != 2 * view.block_size or k <= 0:
        raise NegativeArchiveError("candidate rebuild has invalid n/k/block binding")
    return {
        "construction": canonical,
        "code": code,
        "hx": hx,
        "hz": hz,
        "lx": lx,
        "lz": lz,
        "n": n,
        "k": k,
        "block_size": view.block_size,
    }


def _build_candidate(
    candidate: Mapping[str, Any], construction: Mapping[str, Any]
) -> tuple[dict[str, Any], dict[str, Any]]:
    normalized = normalize_coset_candidate(candidate)
    expected = _expected_construction(normalized)
    if dict(construction) != expected:
        raise NegativeArchiveError("candidate and construction bindings disagree")
    return normalized, _build_construction(expected)


def _candidate_core_from_ranked_row(row: Mapping[str, Any]) -> dict[str, Any]:
    """Extract or reconstruct the exact registered search genotype.

    Early paper-screen artifacts retained the canonical construction and the
    search candidate digest, but compacted away the renderer-v3 genotype
    fields.  The construction contains every mathematical support choice.  In
    that legacy shape we deterministically rebuild every registered genotype
    that could compile to it and accept only the unique one whose digest is
    the artifact's sealed candidate identity.
    """

    identity = (row.get("schema_version"), row.get("representation_id"))
    if identity == (COSET_CANDIDATE_SCHEMA_VERSION, COSET_REPRESENTATION_ID):
        names = (
            "schema_version", "representation_id", "action_id",
            "left_support", "right_support",
        )
    elif identity == (
        COSET_CANDIDATE_SCHEMA_VERSION_V3,
        COSET_REPRESENTATION_ID_V3,
    ):
        names = (
            "schema_version", "representation_id", "renderer_descriptor_id",
            "action_id", "support_split", "left_support", "right_support",
        )
        if row.get("renderer_descriptor_id") != COSET_RENDERER_V3_ID:
            raise NegativeArchiveError(
                "frontier candidate renderer is not registered"
            )
    else:
        genotype_fields = {
            "schema_version", "representation_id", "renderer_descriptor_id",
            "action_id", "support_split", "left_support", "right_support",
        }
        if genotype_fields & set(row):
            raise NegativeArchiveError(
                "frontier candidate representation is not registered"
            )
        compact_fields = {
            "candidate_sha256", "canonical_digest", "construction", "k",
            "n", "required_distance", "source", "target", "target_mode",
            "trial",
        }
        if set(row) != compact_fields:
            raise NegativeArchiveError(
                "frontier compact candidate fields are not exact"
            )
        construction = row.get("construction")
        candidate_sha256 = row.get("candidate_sha256")
        if not isinstance(construction, Mapping) or not _is_sha256(
            candidate_sha256
        ):
            raise NegativeArchiveError(
                "frontier compact candidate identity is incomplete"
            )
        try:
            canonical = normalize_coset_two_block_construction(construction)
        except (KeyError, TypeError, ValueError) as exc:
            raise NegativeArchiveError(
                "frontier compact construction does not replay"
            ) from exc
        if canonical != dict(construction):
            raise NegativeArchiveError(
                "frontier compact construction is not canonical"
            )
        split = [
            len(canonical["left_support"]),
            len(canonical["right_support"]),
        ]
        proposed = (
            {
                "schema_version": COSET_CANDIDATE_SCHEMA_VERSION,
                "representation_id": COSET_REPRESENTATION_ID,
                "action_id": canonical["action_id"],
                "left_support": canonical["left_support"],
                "right_support": canonical["right_support"],
            },
            {
                "schema_version": COSET_CANDIDATE_SCHEMA_VERSION_V3,
                "representation_id": COSET_REPRESENTATION_ID_V3,
                "renderer_descriptor_id": COSET_RENDERER_V3_ID,
                "action_id": canonical["action_id"],
                "support_split": split,
                "left_support": canonical["left_support"],
                "right_support": canonical["right_support"],
            },
        )
        matches: list[dict[str, Any]] = []
        for proposed_core in proposed:
            try:
                normalized = normalize_coset_candidate(proposed_core)
            except (KeyError, TypeError, ValueError):
                continue
            if (
                coset_candidate_digest(normalized) == candidate_sha256
                and _expected_construction(normalized) == canonical
            ):
                matches.append(normalized)
        if len(matches) != 1:
            raise NegativeArchiveError(
                "frontier compact candidate digest is ambiguous or changed"
            )
        return matches[0]
    try:
        core = {name: row[name] for name in names}
        return normalize_coset_candidate(core)
    except (KeyError, TypeError, ValueError) as exc:
        raise NegativeArchiveError(
            "frontier candidate genotype does not replay"
        ) from exc


def _coordinate(key_kind: str, value: Mapping[str, Any]) -> dict[str, Any]:
    payload = {"kind": key_kind, **dict(value)}
    return {**payload, "key_sha256": _sha256(payload)}


def _weight_bucket(weight: int) -> str:
    for upper in (2, 4, 8, 12, 16, 23):
        if weight <= upper:
            lower = 1 if upper == 2 else {4: 3, 8: 5, 12: 9, 16: 13, 23: 17}[upper]
            return f"w{lower}-{upper}"
    return "w24+"


def _shortfall_bucket(shortfall: int) -> str:
    if shortfall <= 0:
        raise NegativeArchiveError("negative witness does not miss its target")
    for upper in (1, 2, 4, 8, 16):
        if shortfall <= upper:
            lower = 1 if upper == 1 else {2: 2, 4: 3, 8: 5, 16: 9}[upper]
            return f"g{lower}-{upper}"
    return "g17+"


def _verified_witness_orbit(
    construction: Mapping[str, Any],
    *,
    hx: np.ndarray,
    hz: np.ndarray,
    support: Sequence[int],
) -> dict[str, Any]:
    """Canonicalize support only under matrix-replayed automorphisms."""

    report = verify_construction_symmetry(
        {"construction": dict(construction)}, hx, hz,
    )
    generators_raw = report.get("verified_generators")
    n = int(hx.shape[1])
    if (
        report.get("verified") is not True
        or not isinstance(generators_raw, list)
        or not generators_raw
    ):
        return {
            "available": False,
            "reason": "no-nontrivial-matrix-replayed-generator",
            "symmetry_report_sha256": report.get("report_sha256"),
        }
    generators: set[tuple[int, ...]] = set()
    for raw in generators_raw:
        if not isinstance(raw, Mapping):
            raise NegativeArchiveError("verified symmetry generator is malformed")
        value = raw.get("qubit_permutation")
        if (
            not isinstance(value, list)
            or any(isinstance(item, bool) or not isinstance(item, int) for item in value)
            or sorted(value) != list(range(n))
        ):
            raise NegativeArchiveError("verified symmetry permutation is invalid")
        permutation = tuple(value)
        inverse = [0] * n
        for source, destination in enumerate(permutation):
            inverse[destination] = source
        generators.add(permutation)
        generators.add(tuple(inverse))
    initial = tuple(sorted(support))
    observed = {initial}
    frontier = [initial]
    while frontier:
        state = frontier.pop()
        for permutation in generators:
            transformed = tuple(sorted(permutation[index] for index in state))
            if transformed in observed:
                continue
            if len(observed) >= _MAX_WITNESS_ORBIT_STATES:
                return {
                    "available": False,
                    "reason": "verified-orbit-exceeds-safe-state-cap",
                    "state_cap": _MAX_WITNESS_ORBIT_STATES,
                    "symmetry_report_sha256": report.get("report_sha256"),
                }
            observed.add(transformed)
            frontier.append(transformed)
    canonical = min(observed)
    return {
        "available": True,
        "canonical_support": list(canonical),
        "orbit_size": len(observed),
        "verified_generator_count": len(generators_raw),
        "symmetry_report_sha256": report.get("report_sha256"),
    }


def _construction_associations(
    construction: Mapping[str, Any],
) -> dict[str, dict[str, Any]]:
    left = list(construction["left_support"])
    right = list(construction["right_support"])
    action_id = str(construction["action_id"])
    return {
        "exact_construction": _coordinate("construction-exact", {
            "construction_sha256": _sha256(construction),
            "action_id": action_id,
            "left_support": left,
            "right_support": right,
        }),
        "action_support_split": _coordinate("construction-action-support-split", {
            "action_id": action_id,
            "support_split": [len(left), len(right)],
        }),
        "action": _coordinate("construction-action", {
            "action_id": action_id,
        }),
    }


def _motif(
    construction: Mapping[str, Any],
    *,
    rebuilt: Mapping[str, Any],
    witness: Mapping[str, Any],
    required_distance: int,
) -> dict[str, Any]:
    canonical_construction = dict(construction)
    view = action_search_view(str(canonical_construction["action_id"]))
    n = int(rebuilt["n"])
    block_size = int(rebuilt["block_size"])
    support = witness.get("support")
    if (
        not isinstance(support, list)
        or any(isinstance(index, bool) or not isinstance(index, int) for index in support)
        or support != sorted(set(support))
        or any(index < 0 or index >= n for index in support)
    ):
        raise NegativeArchiveError("verified witness support is not canonical")
    left_qubits = [index for index in support if index < block_size]
    right_qubits = [index - block_size for index in support if index >= block_size]
    layout = (
        "A-only" if left_qubits and not right_qubits
        else "B-only" if right_qubits and not left_qubits
        else "cross"
    )
    sector = str(witness["sector"])
    weight = int(witness["weight"])
    if (
        isinstance(required_distance, bool)
        or not isinstance(required_distance, int)
        or required_distance <= weight
    ):
        raise NegativeArchiveError(
            "verified witness does not exclude the selected target"
        )
    shortfall = required_distance - weight
    profile = [len(left_qubits), len(right_qubits)]
    orbit = _verified_witness_orbit(
        canonical_construction,
        hx=np.asarray(rebuilt["hx"]),
        hz=np.asarray(rebuilt["hz"]),
        support=support,
    )
    coordinates = {
        "block": _coordinate("witness-block-layout", {
            "sector": sector,
            "layout": layout,
            "block_weight_profile": profile,
            "weight_bucket": _weight_bucket(weight),
        }),
        "action": _coordinate("witness-action-mechanism", {
            "action_id": view.action_id,
            "action_family_bin": view.action_family_bin,
            "subgroup_normal": view.subgroup_normal,
            "sector": sector,
            "layout": layout,
            "block_weight_profile": profile,
            "weight_bucket": _weight_bucket(weight),
        }),
        "support": _coordinate("witness-relative-support", {
            "action_id": view.action_id,
            "sector": sector,
            "layout": layout,
            "weight_bucket": _weight_bucket(weight),
            "left_relative_support": left_qubits,
            "right_relative_support": right_qubits,
        }),
        "shortfall": _coordinate("witness-threshold-shortfall", {
            "action_family_bin": view.action_family_bin,
            "sector": sector,
            "layout": layout,
            "required_distance": required_distance,
            "shortfall_bucket": _shortfall_bucket(shortfall),
        }),
    }
    if orbit.get("available") is True:
        canonical_support = list(orbit["canonical_support"])
        coordinates["orbit"] = _coordinate("witness-verified-action-orbit", {
            "action_id": view.action_id,
            "sector": sector,
            "weight": weight,
            "canonical_support": canonical_support,
        })
    body = {
        "schema_version": NEGATIVE_MOTIF_SCHEMA_VERSION,
        "kind": NEGATIVE_MOTIF_KIND,
        "construction": canonical_construction,
        "construction_associations": _construction_associations(
            canonical_construction
        ),
        "coordinates": coordinates,
        "verified_orbit": orbit,
        "witness": {
            "sector": sector,
            "weight": weight,
            "support": support,
            "left_block_support": left_qubits,
            "right_block_support": right_qubits,
            "block_layout": layout,
            "block_weight_profile": profile,
            "weight_bucket": _weight_bucket(weight),
            "target_required_distance": required_distance,
            "threshold_shortfall": shortfall,
            "threshold_shortfall_bucket": _shortfall_bucket(shortfall),
            "logical_syndrome": witness.get("logical_syndrome"),
        },
    }
    return {**body, "motif_sha256": _sha256(body)}


def _event(
    motif: Mapping[str, Any],
    *,
    source: str,
    evidence_sha256: str,
    artifact_sha256: str | None,
) -> dict[str, Any]:
    if not _is_sha256(evidence_sha256):
        raise NegativeArchiveError("witness evidence has no valid self-hash")
    if artifact_sha256 is not None and not _is_sha256(artifact_sha256):
        raise NegativeArchiveError("Stage-3 artifact has no valid self-hash")
    body = {
        "schema_version": NEGATIVE_EVENT_SCHEMA_VERSION,
        "kind": NEGATIVE_EVENT_KIND,
        "motif": dict(motif),
        "proof": {
            "source": source,
            "evidence_sha256": evidence_sha256,
            "artifact_sha256": artifact_sha256,
            "archive_binding_sha256": _BOUND_SOURCE["binding_sha256"],
        },
    }
    return {**body, "event_sha256": _sha256(body)}


def _stage1_event(row: Mapping[str, Any]) -> dict[str, Any]:
    candidate = row.get("candidate")
    construction = row.get("construction")
    evidence = row.get("low_weight_oracle")
    if not all(isinstance(value, Mapping) for value in (candidate, construction, evidence)):
        raise NegativeArchiveError("Stage-1 row lacks candidate/construction/oracle evidence")
    normalized, rebuilt = _build_candidate(candidate, construction)
    if row.get("candidate_sha256") != coset_candidate_digest(normalized):
        raise NegativeArchiveError("Stage-1 candidate digest does not replay")
    if row.get("n") != rebuilt["n"] or row.get("k") != rebuilt["k"]:
        raise NegativeArchiveError("Stage-1 candidate n/k does not replay")
    required = _candidate_target_required_distance(
        row,
        n=rebuilt["n"],
        k=rebuilt["k"],
        where="Stage-1 candidate",
    )
    failures = verify_css_low_weight_oracle(
        evidence,
        rebuilt["hx"], rebuilt["hz"], rebuilt["lx"], rebuilt["lz"],
        require_current_source=False,
    )
    if failures:
        raise NegativeArchiveError("Stage-1 witness replay failed: " + "; ".join(failures))
    witness = evidence.get("witness")
    if (
        evidence.get("outcome") != "SAT"
        or evidence.get("decision_complete") is not True
        or not isinstance(witness, Mapping)
    ):
        raise NegativeArchiveError("Stage-1 evidence is not a complete SAT witness")
    weight = witness.get("weight")
    if (
        isinstance(weight, bool)
        or not isinstance(weight, int)
        or weight >= required
    ):
        raise NegativeArchiveError("Stage-1 witness does not exclude the final gate")
    normalized_witness = {
        "sector": witness.get("side"),
        "weight": weight,
        "support": witness.get("support"),
        "logical_syndrome": witness.get("logical_syndrome"),
    }
    motif = _motif(
        rebuilt["construction"],
        rebuilt=rebuilt,
        witness=normalized_witness,
        required_distance=required,
    )
    return _event(
        motif,
        source="stage1-low-weight-oracle",
        evidence_sha256=str(evidence.get("evidence_sha256")),
        artifact_sha256=None,
    )


def ingest_stage1_rows(
    path: Path | str | None,
    rows: Iterable[Mapping[str, Any]],
) -> dict[str, Any]:
    """Verify and atomically add complete Stage-1 SAT negatives."""

    events = [_stage1_event(row) for row in rows]
    selected = None if path is None else Path(path)
    return _merge_events(selected, events)


def _strict_jsonl_bytes(payload: bytes, *, where: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(payload.splitlines(), start=1):
        if not line.strip():
            continue
        rows.append(_strict_json_bytes(
            line,
            where=f"{where}:{line_number}",
        ))
    return rows


def _row_canonical_digest(row: Mapping[str, Any]) -> str | None:
    values = []
    for value in (
        row.get("canonical_digest"),
        (
            row.get("structural_novelty", {}).get("canonical_digest")
            if isinstance(row.get("structural_novelty"), Mapping) else None
        ),
        (
            row.get("triage_identity", {}).get("canonical_digest")
            if isinstance(row.get("triage_identity"), Mapping) else None
        ),
    ):
        if _is_sha256(value):
            values.append(str(value))
    if not values:
        return None
    if len(set(values)) != 1:
        raise NegativeArchiveError("Stage-2 ranked row has conflicting digests")
    return values[0]


def _candidate_target_required_distance(
    candidate: Mapping[str, Any],
    *,
    n: int,
    k: int,
    where: str,
) -> int:
    """Replay an explicit target contract or the all-absent legacy policy."""

    contract_fields = (
        "target_mode",
        "target",
        "target_binding_sha256",
        "target_required_distance",
    )
    if all(name not in candidate for name in contract_fields):
        if DEFAULT_TARGET_MODE != TARGET_MODE_GIST:
            raise NegativeArchiveError(
                f"{where} legacy target policy is no longer the default gist"
            )
        required = minimum_target_distance(n, k, DEFAULT_TARGET_MODE)
        if candidate.get("required_distance") != required:
            raise NegativeArchiveError(
                f"{where} legacy target threshold does not replay"
            )
        return required

    raw_mode = candidate.get("target_mode")
    raw_target = candidate.get("target")
    if not isinstance(raw_mode, str) or not isinstance(raw_target, Mapping):
        raise NegativeArchiveError(f"{where} lacks an explicit target binding")
    try:
        mode = validate_target_mode(raw_mode)
        target = validate_target_binding(raw_target, n, k, mode)
        required = minimum_target_distance(n, k, mode)
    except ValueError as exc:
        raise NegativeArchiveError(
            f"{where} target binding does not replay"
        ) from exc
    if target["required_distance"] != required:
        raise NegativeArchiveError(f"{where} target threshold does not replay")
    if (
        "target_binding_sha256" in candidate
        and candidate.get("target_binding_sha256") != target["binding_sha256"]
    ):
        raise NegativeArchiveError(f"{where} target binding mirror changed")
    if (
        "target_required_distance" in candidate
        and candidate.get("target_required_distance") != required
    ):
        raise NegativeArchiveError(f"{where} target threshold mirror changed")
    if (
        "required_distance" in candidate
        and candidate.get("required_distance") != required
    ):
        raise NegativeArchiveError(f"{where} target threshold does not replay")
    return required


def _stage2_basis_event(
    result: Mapping[str, Any],
    candidate: Mapping[str, Any],
) -> dict[str, Any]:
    evidence = result.get("logical_basis_upper_bound")
    construction = candidate.get("construction")
    if not isinstance(evidence, Mapping) or not isinstance(construction, Mapping):
        raise NegativeArchiveError(
            "Stage-2 basis rejection lacks evidence/construction"
        )
    if set(evidence) != {
        "schema_version", "gate", "canonical_digest", "n", "k",
        "required_distance", "witness", "evidence_sha256",
    }:
        raise NegativeArchiveError("Stage-2 basis evidence fields changed")
    _validate_sealed_record(
        evidence,
        hash_field="evidence_sha256",
        where="Stage-2 basis evidence",
    )
    rebuilt = _build_construction(construction)
    if candidate.get("n") != rebuilt["n"] or candidate.get("k") != rebuilt["k"]:
        raise NegativeArchiveError("Stage-2 basis candidate n/k does not replay")
    required = _candidate_target_required_distance(
        candidate,
        n=rebuilt["n"],
        k=rebuilt["k"],
        where="Stage-2 basis candidate",
    )
    digest = result.get("canonical_digest")
    if (
        not _is_sha256(digest)
        or evidence.get("canonical_digest") != digest
        or structural_canonical_digest(rebuilt["code"]) != digest
    ):
        raise NegativeArchiveError("Stage-2 basis candidate digest changed")
    from evaluation.distance_milp import symplectic_weight_witness

    witness = symplectic_weight_witness(rebuilt["code"])
    if not isinstance(witness, Mapping):
        raise NegativeArchiveError("Stage-2 basis witness cannot be rebuilt")
    expected = {
        "schema_version": 1,
        "gate": "qldpc-stage2-logical-basis-upper-bound",
        "canonical_digest": digest,
        "n": rebuilt["n"],
        "k": rebuilt["k"],
        "required_distance": required,
        "witness": dict(witness),
    }
    expected["evidence_sha256"] = _sha256(expected)
    weight = witness.get("weight")
    if (
        dict(evidence) != expected
        or result.get("status") != "REJECTED"
        or result.get("retry_required") is not False
        or result.get("threshold_rejection_proven") is not True
        or result.get("threshold_proof_source")
        != "logical-basis-upper-bound"
        or result.get("distance_upper_bound") != weight
        or isinstance(weight, bool)
        or not isinstance(weight, int)
        or not 1 <= weight < required
    ):
        raise NegativeArchiveError(
            "Stage-2 basis witness does not replay a threshold rejection"
        )
    bits = witness.get("bits")
    if (
        not isinstance(bits, list)
        or len(bits) != rebuilt["n"]
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
    ):
        raise NegativeArchiveError("Stage-2 basis witness bits are invalid")
    vector = np.asarray(bits, dtype=np.uint8)
    side = witness.get("side")
    logicals = (
        rebuilt["lz"] if side == "X"
        else rebuilt["lx"] if side == "Z"
        else None
    )
    if logicals is None:
        raise NegativeArchiveError("Stage-2 basis witness side is invalid")
    motif = _motif(
        rebuilt["construction"],
        rebuilt=rebuilt,
        witness={
            "sector": side,
            "weight": weight,
            "support": [int(index) for index in np.flatnonzero(vector)],
            "logical_syndrome": ((logicals @ vector) & 1).astype(int).tolist(),
        },
        required_distance=required,
    )
    return _event(
        motif,
        source="stage2-logical-basis-upper-bound",
        evidence_sha256=str(evidence["evidence_sha256"]),
        artifact_sha256=None,
    )


def _stage2_sparse_event(
    result: Mapping[str, Any],
    candidate: Mapping[str, Any],
) -> dict[str, Any]:
    evidence = result.get("two_block_sparse_kernel_oracle")
    construction = candidate.get("construction")
    if not isinstance(evidence, Mapping) or not isinstance(construction, Mapping):
        raise NegativeArchiveError("Stage-2 sparse-kernel result lacks evidence/construction")
    rebuilt = _build_construction(construction)
    if (
        candidate.get("n") != rebuilt["n"]
        or candidate.get("k") != rebuilt["k"]
    ):
        raise NegativeArchiveError("Stage-2 candidate n/k does not replay")
    required = _candidate_target_required_distance(
        candidate,
        n=rebuilt["n"],
        k=rebuilt["k"],
        where="Stage-2 candidate",
    )
    failures = verify_two_block_sparse_kernel_oracle(
        evidence,
        rebuilt["hx"], rebuilt["hz"], rebuilt["lx"], rebuilt["lz"],
        block_size=rebuilt["block_size"],
        require_current_source=True,
    )
    if failures:
        raise NegativeArchiveError(
            "Stage-2 sparse-kernel witness replay failed: " + "; ".join(failures)
        )
    witness = evidence.get("witness")
    weight = witness.get("weight") if isinstance(witness, Mapping) else None
    if (
        result.get("status") != "REJECTED"
        or result.get("threshold_proof_source")
        != "two-block-sparse-kernel-oracle"
        or evidence.get("outcome") != "SAT"
        or evidence.get("decision_complete") is not True
        or not isinstance(witness, Mapping)
        or isinstance(weight, bool)
        or not isinstance(weight, int)
        or weight >= required
    ):
        raise NegativeArchiveError("Stage-2 evidence is not a threshold-rejecting SAT witness")
    motif = _motif(
        rebuilt["construction"],
        rebuilt=rebuilt,
        witness={
            "sector": witness.get("side"),
            "weight": weight,
            "support": witness.get("support"),
            "logical_syndrome": witness.get("logical_syndrome"),
        },
        required_distance=required,
    )
    return _event(
        motif,
        source="stage2-two-block-sparse-kernel",
        evidence_sha256=str(evidence.get("evidence_sha256")),
        artifact_sha256=None,
    )


def _stage2_global_event(
    result: Mapping[str, Any],
    candidate: Mapping[str, Any],
) -> dict[str, Any]:
    """Replay one unrestricted Stage-2 SAT from its authoritative cache.

    The compact ladder in ``stage2-summary.json`` is deliberately not a proof
    artifact: it contains only a witness synopsis.  The cache envelope is the
    durable trust boundary, so we verify its self-hash, reconstruct its exact
    producer binding from the ranked candidate and current matrices, and then
    replay the complete X/Z oracle evidence before learning from the witness.
    """

    ladder = result.get("compact_low_weight_sat_ladder")
    construction = candidate.get("construction")
    if not isinstance(ladder, Mapping) or not isinstance(construction, Mapping):
        raise NegativeArchiveError(
            "Stage-2 global low-weight result lacks ladder/construction"
        )
    rebuilt = _build_construction(construction)
    if (
        candidate.get("n") != rebuilt["n"]
        or candidate.get("k") != rebuilt["k"]
    ):
        raise NegativeArchiveError("Stage-2 candidate n/k does not replay")
    required = _candidate_target_required_distance(
        candidate,
        n=rebuilt["n"],
        k=rebuilt["k"],
        where="Stage-2 candidate",
    )
    digest = result.get("canonical_digest")
    max_weight = ladder.get("max_weight")
    if (
        not _is_sha256(digest)
        or result.get("status") != "REJECTED"
        or result.get("retry_required", False) is not False
        or result.get("threshold_rejection_proven") is not True
        or result.get("threshold_proof_source") != "compact-low-weight-sat"
        or ladder.get("schema_version") != 1
        or ladder.get("gate") != "qldpc-stage2-compact-low-weight-gate"
        or ladder.get("outcome") != "SAT"
        or ladder.get("decision_complete") is not True
        or ladder.get("retryable") is not False
        or isinstance(max_weight, bool)
        or not isinstance(max_weight, int)
        or not 1 <= max_weight < required
    ):
        raise NegativeArchiveError(
            "Stage-2 global evidence is not a threshold-rejecting SAT result"
        )

    raw_cache_path = ladder.get("cache_path")
    if not isinstance(raw_cache_path, str) or not raw_cache_path:
        raise NegativeArchiveError("Stage-2 global SAT ladder has no cache path")
    cache_path = Path(raw_cache_path).expanduser()
    if not cache_path.is_absolute():
        raise NegativeArchiveError("Stage-2 global SAT cache path must be absolute")
    envelope = _strict_json_bytes(
        _read_regular_bytes(cache_path, limit=_MAX_STAGE3_BYTES),
        where=str(cache_path),
    )
    if set(envelope) != {
        "schema_version", "kind", "binding", "evidence", "cache_sha256",
    }:
        raise NegativeArchiveError("Stage-2 global SAT cache envelope changed")
    _validate_sealed_record(
        envelope,
        hash_field="cache_sha256",
        where="Stage-2 global SAT cache",
    )
    binding = envelope.get("binding")
    evidence = envelope.get("evidence")
    if (
        envelope.get("schema_version") != 1
        or envelope.get("kind") != "qldpc-stage2-compact-low-weight-cache"
        or not isinstance(binding, Mapping)
        or not isinstance(evidence, Mapping)
    ):
        raise NegativeArchiveError("Stage-2 global SAT cache schema is invalid")

    # Use the producer's fixed retained-field projection and binding builder.
    # ``audit_candidate_pool.py`` is part of ``_BOUND_SOURCE`` above, so a
    # producer change necessarily versions the archive instead of silently
    # changing replay semantics.
    from scripts.audit_candidate_pool import (
        _compact_low_weight_cache_binding,
        _construction_candidate,
    )

    try:
        producer_candidate = _construction_candidate(candidate, str(digest))
        expected_binding = _compact_low_weight_cache_binding(
            producer_candidate,
            (
                rebuilt["hx"], rebuilt["hz"], rebuilt["lx"], rebuilt["lz"],
            ),
            max_weight=max_weight,
        )
    except (KeyError, TypeError, ValueError, RuntimeError) as exc:
        raise NegativeArchiveError(
            "Stage-2 global SAT cache binding cannot be reconstructed"
        ) from exc
    if dict(binding) != expected_binding:
        raise NegativeArchiveError("Stage-2 global SAT cache binding mismatch")

    failures = verify_css_low_weight_oracle(
        evidence,
        rebuilt["hx"], rebuilt["hz"], rebuilt["lx"], rebuilt["lz"],
        require_current_source=True,
    )
    if failures:
        raise NegativeArchiveError(
            "Stage-2 global low-weight witness replay failed: "
            + "; ".join(failures)
        )
    witness = evidence.get("witness")
    weight = witness.get("weight") if isinstance(witness, Mapping) else None
    if (
        evidence.get("outcome") != "SAT"
        or evidence.get("decision_complete") is not True
        or evidence.get("retryable") is not False
        or evidence.get("max_weight") != max_weight
        or not isinstance(witness, Mapping)
        or isinstance(weight, bool)
        or not isinstance(weight, int)
        or not 1 <= weight < required
        or result.get("distance_upper_bound") != weight
        or ladder.get("distance_lower_bound") is not None
        or ladder.get("witness") != witness
        or ladder.get("evidence_sha256") != evidence.get("evidence_sha256")
    ):
        raise NegativeArchiveError(
            "Stage-2 global SAT summary/cache semantics disagree"
        )
    motif = _motif(
        rebuilt["construction"],
        rebuilt=rebuilt,
        witness={
            "sector": witness.get("side"),
            "weight": weight,
            "support": witness.get("support"),
            "logical_syndrome": witness.get("logical_syndrome"),
        },
        required_distance=required,
    )
    return _event(
        motif,
        source="stage2-global-low-weight",
        # Retain the proof envelope identity, not merely the synopsis' inner
        # evidence hash, so exact candidate/matrix/runtime provenance remains
        # addressable from every archive event.
        evidence_sha256=str(envelope.get("cache_sha256")),
        artifact_sha256=None,
    )


def _stage2_summary_events(summary: Mapping[str, Any]) -> list[dict[str, Any]]:
    if (
        summary.get("schema_version") != 1
        or summary.get("gate") != "qldpc-proof-oriented-candidate-pool"
        or not isinstance(summary.get("results"), list)
    ):
        raise NegativeArchiveError("Stage-2 summary envelope is invalid")
    selected_results: list[tuple[str, Mapping[str, Any]]] = []
    for raw in summary["results"]:
        if not isinstance(raw, Mapping):
            raise NegativeArchiveError("Stage-2 summary result is not an object")
        basis = raw.get("logical_basis_upper_bound")
        sparse = raw.get("two_block_sparse_kernel_oracle")
        ladder = raw.get("compact_low_weight_sat_ladder")
        basis_reject = (
            isinstance(basis, Mapping)
            and raw.get("threshold_proof_source")
            == "logical-basis-upper-bound"
        )
        sparse_sat = isinstance(sparse, Mapping) and sparse.get("outcome") == "SAT"
        global_sat = isinstance(ladder, Mapping) and ladder.get("outcome") == "SAT"
        if sum((basis_reject, sparse_sat, global_sat)) > 1:
            raise NegativeArchiveError(
                "Stage-2 result claims multiple negative terminal sources"
            )
        if basis_reject:
            selected_results.append(("basis", raw))
        elif sparse_sat:
            selected_results.append(("sparse", raw))
        elif global_sat:
            selected_results.append(("global", raw))
        elif raw.get("threshold_proof_source") == "logical-basis-upper-bound":
            raise NegativeArchiveError(
                "Stage-2 basis rejection lost its evidence"
            )
        elif raw.get("threshold_proof_source") == "two-block-sparse-kernel-oracle":
            raise NegativeArchiveError("Stage-2 sparse-kernel rejection lost its evidence")
        elif raw.get("threshold_proof_source") == "compact-low-weight-sat":
            raise NegativeArchiveError("Stage-2 global rejection lost its SAT ladder")
    if not selected_results:
        return []
    ranked_raw = summary.get("ranked_output")
    if not isinstance(ranked_raw, str) or not ranked_raw:
        raise NegativeArchiveError("Stage-2 summary has no ranked output binding")
    ranked_path = Path(ranked_raw).expanduser()
    if not ranked_path.is_absolute():
        raise NegativeArchiveError("Stage-2 ranked output path must be absolute")
    rows = _strict_jsonl_bytes(
        _read_regular_bytes(ranked_path, limit=_MAX_STAGE3_BYTES),
        where=str(ranked_path),
    )
    by_digest: dict[str, list[Mapping[str, Any]]] = {}
    for row in rows:
        digest = _row_canonical_digest(row)
        if digest is not None:
            by_digest.setdefault(digest, []).append(row)
    events = []
    for source, result in selected_results:
        digest = result.get("canonical_digest")
        if not _is_sha256(digest):
            raise NegativeArchiveError("Stage-2 result canonical digest is invalid")
        matches = by_digest.get(str(digest), [])
        if len(matches) != 1:
            raise NegativeArchiveError(
                "Stage-2 negative result does not resolve to one ranked candidate"
            )
        if source == "basis":
            events.append(_stage2_basis_event(result, matches[0]))
        elif source == "sparse":
            events.append(_stage2_sparse_event(result, matches[0]))
        else:
            events.append(_stage2_global_event(result, matches[0]))
    return events


def ingest_stage2_paths(
    archive_path: Path | str | None,
    paths: Sequence[Path | str],
) -> dict[str, Any]:
    """Replay restricted and unrestricted SAT negatives from Stage-2."""

    events: list[dict[str, Any]] = []
    for raw_path in paths:
        path = Path(raw_path).expanduser()
        if not path.is_absolute():
            raise NegativeArchiveError("Stage-2 negative input path must be absolute")
        summary = _strict_json_bytes(
            _read_regular_bytes(path, limit=_MAX_STAGE3_BYTES),
            where=str(path),
        )
        events.extend(_stage2_summary_events(summary))
    selected = None if archive_path is None else Path(archive_path)
    return _merge_events(selected, events)


def _array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode("ascii"))
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _unpack_operator(record: Mapping[str, Any]) -> np.ndarray:
    try:
        length = int(record["length"])
        packed = bytes.fromhex(str(record["packed_hex"]))
    except (KeyError, TypeError, ValueError) as exc:
        raise NegativeArchiveError("Stage-3 packed operator is invalid") from exc
    if length < 1:
        raise NegativeArchiveError("Stage-3 packed operator length is invalid")
    vector = np.unpackbits(
        np.frombuffer(packed, dtype=np.uint8), bitorder="little"
    )[:length].astype(np.uint8)
    canonical = {
        "length": int(vector.size),
        "weight": int(vector.sum()),
        "packed_hex": np.packbits(vector, bitorder="little").tobytes().hex(),
        "sha256": hashlib.sha256(f"{vector.size}:".encode() + np.packbits(
            vector, bitorder="little"
        ).tobytes()).hexdigest(),
    }
    if canonical != dict(record):
        raise NegativeArchiveError("Stage-3 packed operator metadata/hash mismatch")
    return vector


def _frontier_direction_specs(
    rebuilt: Mapping[str, Any],
) -> list[tuple[str, int, str, np.ndarray, np.ndarray]]:
    return [
        ("Z", index, "hx", rebuilt["hx"], rebuilt["lx"][index])
        for index in range(len(rebuilt["lx"]))
    ] + [
        ("X", index, "hz", rebuilt["hz"], rebuilt["lz"][index])
        for index in range(len(rebuilt["lz"]))
    ]


def _frontier_events(
    artifact: Mapping[str, Any],
    *,
    artifact_file_sha256: str,
) -> list[dict[str, Any]]:
    """Replay paper-standard exact-ILP counterexamples into search memory."""

    if not _is_sha256(artifact_file_sha256):
        raise NegativeArchiveError("frontier artifact file hash is invalid")
    threshold_only = artifact.get("threshold_only")
    claim = artifact.get("candidate")
    directions = artifact.get("directions")
    if (
        artifact.get("schema_version") != FRONTIER_SCHEMA_VERSION
        or artifact.get("gate") != FRONTIER_GATE
        or artifact.get("status") != "REJECTED"
        or not isinstance(threshold_only, bool)
        or not isinstance(claim, Mapping)
        or not isinstance(claim.get("construction"), Mapping)
        or not isinstance(directions, list)
        or not directions
    ):
        raise NegativeArchiveError(
            "frontier artifact is not a terminal rejected CSS screen"
        )

    core = _candidate_core_from_ranked_row(claim)
    candidate_sha256 = claim.get("candidate_sha256")
    if (
        not _is_sha256(candidate_sha256)
        or candidate_sha256 != coset_candidate_digest(core)
        or dict(claim["construction"]) != _expected_construction(core)
    ):
        raise NegativeArchiveError(
            "frontier candidate genotype/construction binding does not replay"
        )
    rebuilt = _build_construction(claim["construction"])
    if claim.get("n") != rebuilt["n"] or claim.get("k") != rebuilt["k"]:
        raise NegativeArchiveError("frontier candidate n/k does not replay")
    canonical_digest = _row_canonical_digest(claim)
    if (
        not _is_sha256(canonical_digest)
        or canonical_digest != structural_canonical_digest(rebuilt["code"])
    ):
        raise NegativeArchiveError(
            "frontier candidate canonical digest does not replay"
        )
    required = _candidate_target_required_distance(
        claim,
        n=rebuilt["n"],
        k=rebuilt["k"],
        where="frontier candidate",
    )
    specs = _frontier_direction_specs(rebuilt)
    geometry = {
        "n": rebuilt["n"],
        "k": rebuilt["k"],
        "required_distance": required,
        "expected_directions": len(specs),
    }
    if (
        artifact.get("required_distance") != required
        or artifact.get("reconstructed_parameters") != geometry
        or artifact.get("expected_directions") != len(specs)
        or artifact.get("completed_directions") != len(directions)
    ):
        raise NegativeArchiveError(
            "frontier artifact geometry/envelope does not replay"
        )

    seen_positions: set[int] = set()
    events: list[dict[str, Any]] = []
    low_count = 0
    for raw in directions:
        if not isinstance(raw, Mapping):
            raise NegativeArchiveError("frontier direction is not an object")
        position = raw.get("position")
        if (
            isinstance(position, bool)
            or not isinstance(position, int)
            or not 0 <= position < len(specs)
            or position in seen_positions
        ):
            raise NegativeArchiveError(
                "frontier direction position is invalid or duplicated"
            )
        seen_positions.add(position)
        objective = raw.get("objective")
        if (
            isinstance(objective, bool)
            or not isinstance(objective, int)
            or objective >= required
        ):
            # Only a concrete sub-threshold operator affects search. Other
            # completed/unknown directions remain inert artifact provenance.
            continue

        logical_type, logical_index, check_name, checks, target = specs[position]
        expected_formulation = (
            CSS_THRESHOLD_FORMULATION
            if threshold_only else CSS_EXACT_FORMULATION
        )
        if (
            raw.get("logical_type") != logical_type
            or raw.get("logical_index") != logical_index
            or raw.get("check_matrix") != check_name
            or raw.get("target_logical") != pack_vector(target)
            or raw.get("formulation") != expected_formulation
            or raw.get("solver") != "scipy.optimize.milp"
            or raw.get("backend") != "HiGHS"
            or raw.get("solver_workers") != 1
            or raw.get("witness_verified") is not True
            or raw.get("witness_failures") != []
            or (
                threshold_only
                and raw.get("max_weight") != required - 1
            )
            or (
                not threshold_only
                and raw.get("max_weight") is not None
            )
        ):
            raise NegativeArchiveError(
                "frontier low witness direction binding changed"
            )
        is_zero_gap_optimum = bool(
            raw.get("success") is True
            and type(raw.get("status")) is int
            and raw.get("status") == 0
            and _is_finite_number(raw.get("mip_gap"))
            and float(raw["mip_gap"]) == 0.0
            and _is_finite_number(raw.get("mip_dual_bound"))
            and abs(float(raw["mip_dual_bound"]) - objective) <= 1e-7
        )
        is_timeout_incumbent = bool(
            threshold_only
            and raw.get("formulation") == CSS_THRESHOLD_FORMULATION
            and raw.get("has_incumbent") is True
            and raw.get("optimal") is False
            and raw.get("outcome") == "incumbent_witness"
            and raw.get("success") is False
            and type(raw.get("status")) is int
            and raw.get("status") == 1
            and raw.get("threshold_infeasible") is False
            and _is_finite_number(raw.get("mip_primal_bound"))
            and abs(float(raw["mip_primal_bound"]) - objective) <= 1e-7
            and _is_finite_number(raw.get("mip_dual_bound"))
            and float(raw["mip_dual_bound"]) <= objective + 1e-7
            and _is_finite_number(raw.get("mip_gap"))
            and 0.0 <= float(raw["mip_gap"])
        )
        if is_zero_gap_optimum:
            failures = verify_direction_evidence(dict(raw), checks, target)
            source = "frontier-exact-ilp"
        elif is_timeout_incumbent:
            failures = verify_css_witness(dict(raw), checks, target)
            source = "frontier-replayed-incumbent"
        else:
            failures = [
                "stored solver result is neither a zero-gap optimum "
                "nor a bound timeout incumbent"
            ]
        if failures:
            raise NegativeArchiveError(
                "frontier low witness replay failed: " + "; ".join(failures)
            )
        vector = _unpack_operator(raw["operator"])
        if objective != int(vector.sum()):
            raise NegativeArchiveError(
                "frontier low witness objective changed after unpacking"
            )
        logicals = rebuilt["lx"] if logical_type == "Z" else rebuilt["lz"]
        logical_syndrome = ((logicals @ vector) & 1).astype(int).tolist()
        motif = _motif(
            rebuilt["construction"],
            rebuilt=rebuilt,
            witness={
                "sector": logical_type,
                "weight": objective,
                "support": [int(index) for index in np.flatnonzero(vector)],
                "logical_syndrome": logical_syndrome,
            },
            required_distance=required,
        )
        evidence_sha256 = _sha256({
            "schema_version": 1,
            "kind": "qcode-frontier-exact-ilp-negative-binding",
            "artifact_file_sha256": artifact_file_sha256,
            "candidate_sha256": candidate_sha256,
            "position": position,
            "direction": dict(raw),
        })
        events.append(_event(
            motif,
            source=source,
            evidence_sha256=evidence_sha256,
            artifact_sha256=artifact_file_sha256,
        ))
        low_count += 1

    stored_low_count = artifact.get("low_witnesses")
    if (
        isinstance(stored_low_count, bool)
        or not isinstance(stored_low_count, int)
        or stored_low_count != low_count
        or low_count < 1
    ):
        raise NegativeArchiveError(
            "frontier artifact low-witness count does not replay"
        )
    return events


def ingest_frontier_paths(
    archive_path: Path | str | None,
    paths: Sequence[Path | str],
) -> dict[str, Any]:
    """Verify exact-ILP rejection artifacts and commit them atomically."""

    events: list[dict[str, Any]] = []
    for raw_path in paths:
        path = Path(raw_path).expanduser()
        if not path.is_absolute():
            raise NegativeArchiveError(
                "frontier negative input path must be absolute"
            )
        payload = _read_regular_bytes(path, limit=_MAX_STAGE3_BYTES)
        artifact = _strict_json_bytes(payload, where=str(path))
        events.extend(_frontier_events(
            artifact,
            artifact_file_sha256=hashlib.sha256(payload).hexdigest(),
        ))
    selected = None if archive_path is None else Path(archive_path)
    return _merge_events(selected, events)


def _validate_sat_binding(
    evidence: Mapping[str, Any],
    *,
    sector: str,
    checks: np.ndarray,
    logicals: np.ndarray,
    canonical_digest: str,
) -> None:
    unsigned = dict(evidence)
    evidence_sha = unsigned.pop("evidence_sha256", None)
    if not _is_sha256(evidence_sha) or evidence_sha != _sha256(unsigned):
        raise NegativeArchiveError("Stage-3 SAT evidence self-hash mismatch")
    instance = evidence.get("instance")
    if not isinstance(instance, Mapping):
        raise NegativeArchiveError("Stage-3 SAT evidence has no instance binding")
    instance_unsigned = dict(instance)
    binding_sha = instance_unsigned.pop("binding_sha256", None)
    if not _is_sha256(binding_sha) or binding_sha != _sha256(instance_unsigned):
        raise NegativeArchiveError("Stage-3 SAT instance self-hash mismatch")
    checkpoint = instance.get("checkpoint_identity")
    if not (
        evidence.get("schema_version") == SAT_EVIDENCE_SCHEMA_VERSION
        and evidence.get("evidence_kind") == SAT_EVIDENCE_KIND
        and evidence.get("formulation") == SAT_FORMULATION
        and evidence.get("outcome") == "sat"
        and evidence.get("decision_complete") is True
        and evidence.get("success") is True
        and evidence.get("retryable") is False
        and evidence.get("threshold_infeasible") is False
        and evidence.get("sector") == sector
        and instance.get("sector") == sector
        and evidence.get("max_weight") == instance.get("max_weight")
        and evidence.get("partition_index") == instance.get("partition_index")
        and evidence.get("anchor_indices") == instance.get("anchor_indices")
        and evidence.get("backend") == instance.get("backend")
        and instance.get("n") == int(checks.shape[1])
        and instance.get("num_checks") == int(checks.shape[0])
        and instance.get("num_logicals") == int(logicals.shape[0])
        and instance.get("check_matrix_sha256") == _array_sha256("checks", checks)
        and instance.get("target_logicals_sha256") == _array_sha256("logicals", logicals)
        and isinstance(instance.get("source_sha256"), str)
        and _is_sha256(instance.get("source_sha256"))
        and isinstance(checkpoint, Mapping)
        and checkpoint.get("stage3_gate") == STAGE3_GATE
        and checkpoint.get("candidate_digest") == canonical_digest
    ):
        raise NegativeArchiveError("Stage-3 SAT evidence binding does not replay")
    failures = verify_css_threshold_sat_witness(evidence, checks, logicals)
    if failures:
        raise NegativeArchiveError("Stage-3 SAT witness replay failed: " + "; ".join(failures))


def _stage3_events(artifact: Mapping[str, Any]) -> list[dict[str, Any]]:
    unsigned = dict(artifact)
    artifact_sha = unsigned.pop("artifact_sha256", None)
    if not _is_sha256(artifact_sha) or artifact_sha != _sha256(unsigned):
        raise NegativeArchiveError("Stage-3 artifact self-hash mismatch")
    if (
        artifact.get("schema_version") != STAGE3_SCHEMA_VERSION
        or artifact.get("gate") != STAGE3_GATE
        or artifact.get("status") != "REJECTED"
    ):
        raise NegativeArchiveError("Stage-3 artifact is not a rejected SAT screen")
    claim = artifact.get("candidate")
    if not isinstance(claim, Mapping) or not isinstance(claim.get("construction"), Mapping):
        raise NegativeArchiveError("Stage-3 artifact has no compact construction")
    rebuilt = _build_construction(claim["construction"])
    canonical_digest = claim.get("canonical_digest")
    if not _is_sha256(canonical_digest):
        raise NegativeArchiveError("Stage-3 candidate canonical digest is invalid")
    if (
        claim.get("n") != rebuilt["n"]
        or claim.get("k") != rebuilt["k"]
    ):
        raise NegativeArchiveError("Stage-3 candidate n/k does not replay")
    required = _candidate_target_required_distance(
        claim,
        n=rebuilt["n"],
        k=rebuilt["k"],
        where="Stage-3 candidate",
    )
    if (
        artifact.get("target_mode") != claim.get("target_mode")
        or artifact.get("target") != claim.get("target")
        or artifact.get("required_distance") != required
    ):
        raise NegativeArchiveError(
            "Stage-3 artifact target contract does not replay"
        )
    wrappers = artifact.get("low_witnesses")
    units = artifact.get("units")
    if not isinstance(wrappers, list) or not wrappers or not isinstance(units, list):
        raise NegativeArchiveError("Stage-3 artifact has no indexed low witnesses")
    unit_index: dict[str, list[Mapping[str, Any]]] = {}
    for unit in units:
        if not isinstance(unit, Mapping) or not isinstance(unit.get("solver_evidence"), Mapping):
            continue
        evidence_sha = unit["solver_evidence"].get("evidence_sha256")
        if _is_sha256(evidence_sha):
            unit_index.setdefault(str(evidence_sha), []).append(unit)
    events: list[dict[str, Any]] = []
    for wrapper in wrappers:
        if not isinstance(wrapper, Mapping) or not isinstance(wrapper.get("solver_evidence"), Mapping):
            raise NegativeArchiveError("Stage-3 low-witness wrapper is invalid")
        evidence = wrapper["solver_evidence"]
        evidence_sha = evidence.get("evidence_sha256")
        matches = [
            unit for unit in unit_index.get(str(evidence_sha), [])
            if unit.get("sector") == wrapper.get("sector")
            and unit.get("partition_index") == wrapper.get("partition_index")
            and unit.get("anchor_cube") == wrapper.get("anchor_cube")
        ]
        if len(matches) != 1 or matches[0].get("phase") not in {
            "lower", "lower-global", "upper",
        }:
            raise NegativeArchiveError("Stage-3 low witness is not bound to one proof unit")
        unit = matches[0]
        sector = wrapper.get("sector")
        if sector == "X":
            checks, logicals = rebuilt["hz"], rebuilt["lz"]
        elif sector == "Z":
            checks, logicals = rebuilt["hx"], rebuilt["lx"]
        else:
            raise NegativeArchiveError("Stage-3 low witness sector is invalid")
        expected_threshold = required if unit["phase"] == "upper" else required - 1
        if evidence.get("max_weight") != expected_threshold:
            raise NegativeArchiveError("Stage-3 low witness used the wrong phase threshold")
        _validate_sat_binding(
            evidence,
            sector=str(sector),
            checks=checks,
            logicals=logicals,
            canonical_digest=str(canonical_digest),
        )
        vector = _unpack_operator(evidence["operator"])
        weight = int(vector.sum())
        if evidence.get("objective") != weight or weight >= required:
            raise NegativeArchiveError("Stage-3 witness does not exclude the final gate")
        witness = {
            "sector": sector,
            "weight": weight,
            "support": [int(index) for index in np.flatnonzero(vector)],
            "logical_syndrome": evidence.get("logical_syndrome"),
        }
        motif = _motif(
            rebuilt["construction"],
            rebuilt=rebuilt,
            witness=witness,
            required_distance=required,
        )
        events.append(_event(
            motif,
            source="stage3-threshold-sat",
            evidence_sha256=str(evidence_sha),
            artifact_sha256=str(artifact_sha),
        ))
    return events


def ingest_stage3_artifact(
    path: Path | str | None,
    artifact: Mapping[str, Any],
) -> dict[str, Any]:
    """Verify a complete Stage-3 rejection before atomically archiving it."""

    events = _stage3_events(artifact)
    selected = None if path is None else Path(path)
    return _merge_events(selected, events)


def ingest_stage3_paths(
    archive_path: Path | str | None,
    paths: Sequence[Path | str],
) -> dict[str, Any]:
    """Verify all configured Stage-3 artifacts, then commit them together."""

    events: list[dict[str, Any]] = []
    for raw_path in paths:
        path = Path(raw_path).expanduser()
        if not path.is_absolute():
            raise NegativeArchiveError("Stage-3 negative input path must be absolute")
        payload = _read_regular_bytes(path, limit=_MAX_STAGE3_BYTES)
        artifact = _strict_json_bytes(payload, where=str(path))
        events.extend(_stage3_events(artifact))
    selected = None if archive_path is None else Path(archive_path)
    return _merge_events(selected, events)


def _configured_paths(environment_name: str, *, label: str) -> tuple[Path, ...]:
    raw = os.environ.get(environment_name, "")
    if not raw:
        return ()
    paths = tuple(Path(item).expanduser() for item in raw.split(os.pathsep) if item)
    if not paths or any(not path.is_absolute() for path in paths):
        raise NegativeArchiveError(f"configured {label} negative paths must be absolute")
    if len(set(paths)) != len(paths):
        raise NegativeArchiveError(f"configured {label} negative paths contain duplicates")
    return paths


def configured_stage2_paths() -> tuple[Path, ...]:
    return _configured_paths(STAGE2_NEGATIVE_INPUTS_ENV, label="Stage-2")


def configured_stage3_paths() -> tuple[Path, ...]:
    return _configured_paths(STAGE3_NEGATIVE_INPUTS_ENV, label="Stage-3")


def configured_frontier_paths() -> tuple[Path, ...]:
    return _configured_paths(FRONTIER_NEGATIVE_INPUTS_ENV, label="frontier")


def _candidate_associations(candidate: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    normalized = normalize_coset_candidate(candidate)
    return _construction_associations(_expected_construction(normalized))


def _construction_penalty_from_counts(counts: Mapping[str, int]) -> float:
    # A future witness is not known when a parent is scored.  Penalize only
    # source-owned construction features statistically associated with
    # *distinct verified witness motifs*.  One negative in a same-size block
    # therefore cannot poison unrelated candidates.
    exact = min(int(counts.get("exact_construction", 0)), 4)
    action_split = min(int(counts.get("action_support_split", 0)), 8)
    action = min(int(counts.get("action", 0)), 8)
    penalty = (
        (0.0 if exact == 0 else 0.24 + 0.025 * (exact - 1))
        + 0.008 * action_split
        + 0.002 * action
    )
    return min(0.32, round(penalty, 6))


def _witness_penalty_from_counts(counts: Mapping[str, int]) -> float:
    """Score direct repeats only after the row's witness was replayed."""

    block = min(int(counts.get("block", 0)), 8)
    action = min(int(counts.get("action", 0)), 8)
    orbit = min(int(counts.get("orbit", 0)), 8)
    support = min(int(counts.get("support", 0)), 8)
    return min(0.28, round(
        0.004 * block
        + 0.008 * action
        + 0.018 * orbit
        + 0.012 * support,
        6,
    ))


def annotate_rows(
    path: Path | str | None,
    rows: Iterable[dict[str, Any]],
) -> dict[str, Any]:
    """Attach deterministic archive match counts and penalties to rows."""

    archive = load_archive(path)
    # Count distinct witness motifs, not duplicate solver/artifact events.
    key_motifs: dict[str, set[str]] = {}
    for motif_sha, aggregate in archive["motifs"].items():
        for coordinate in aggregate["motif"]["construction_associations"].values():
            key_motifs.setdefault(str(coordinate["key_sha256"]), set()).add(motif_sha)
    penalized = 0
    maximum = 0.0
    for row in rows:
        coordinates = _candidate_associations(row["candidate"])
        counts = {
            name: len(key_motifs.get(str(coordinate["key_sha256"]), set()))
            for name, coordinate in coordinates.items()
        }
        construction_penalty = _construction_penalty_from_counts(counts)
        witness_counts = {
            "block": 0,
            "action": 0,
            "orbit": 0,
            "support": 0,
        }
        verified_terminal_motif: Mapping[str, Any] | None = None
        if (
            row.get("oracle_outcome") == "SAT"
            and row.get("threshold_rejected") is True
            and isinstance(row.get("low_weight_oracle"), Mapping)
        ):
            # This performs the full matrix/evidence replay again.  A caller
            # cannot attach an arbitrary witness merely to manipulate score.
            event = _stage1_event(row)
            motif = event["motif"]
            verified_terminal_motif = motif
            for name, coordinate in motif["coordinates"].items():
                aggregate = archive["coordinate_aggregates"].get(
                    coordinate["key_sha256"]
                )
                if isinstance(aggregate, Mapping):
                    witness_counts[name] = int(aggregate["motif_count"])
        witness_penalty = _witness_penalty_from_counts(witness_counts)
        penalty = min(0.40, round(
            construction_penalty + witness_penalty,
            6,
        ))
        row["negative_archive_match_counts"] = counts
        row["negative_archive_coordinate_sha256"] = {
            name: coordinate["key_sha256"]
            for name, coordinate in coordinates.items()
        }
        row["negative_archive_penalty"] = penalty
        row["negative_archive_penalty_components"] = {
            "construction_proxy": construction_penalty,
            "verified_witness_mechanism": witness_penalty,
        }
        row["negative_archive_witness_match_counts"] = witness_counts
        row["negative_archive_witness_motif_sha256"] = (
            None
            if verified_terminal_motif is None
            else verified_terminal_motif["motif_sha256"]
        )
        if penalty > 0:
            penalized += 1
            maximum = max(maximum, penalty)
    summary = _archive_summary(archive)
    summary.update({
        "penalized_candidates": penalized,
        "maximum_penalty": maximum,
    })
    return summary


def feedback_lines(
    archive: Mapping[str, Any],
    *,
    limit: int = 8,
) -> list[str]:
    """Render stable, mutation-oriented feedback from the strongest motifs."""

    validated = _validate_archive(archive)
    ranked = sorted(
        validated["coordinate_aggregates"].values(),
        key=lambda item: (
            -int(item["motif_count"]),
            -int(item["event_count"]),
            str(item["coordinate"]["key_sha256"]),
        ),
    )[:max(0, int(limit))]
    lines = []
    for aggregate in ranked:
        coordinate = dict(aggregate["coordinate"])
        key = str(coordinate.pop("key_sha256"))
        kind = str(coordinate.pop("kind"))
        lines.append(
            "  mechanism={kind} key={key} distinct_motifs={motifs} "
            "verified_events={events} features={features}".format(
                kind=kind,
                key=key[:12],
                motifs=aggregate["motif_count"],
                events=aggregate["event_count"],
                features=json.dumps(
                    coordinate,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                    allow_nan=False,
                ),
            )
        )
    return lines


def _main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Ingest independently replayed Stage-3 coset negatives",
    )
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--stage2-summary", action="append", default=[], type=Path)
    parser.add_argument("--stage3-artifact", action="append", default=[], type=Path)
    parser.add_argument("--frontier-artifact", action="append", default=[], type=Path)
    arguments = parser.parse_args(argv)
    if not arguments.archive.is_absolute():
        parser.error("--archive must be absolute")
    if not (
        arguments.stage2_summary
        or arguments.stage3_artifact
        or arguments.frontier_artifact
    ):
        parser.error(
            "at least one Stage-2, Stage-3, or frontier artifact is required"
        )
    added = 0
    if arguments.stage2_summary:
        result = ingest_stage2_paths(arguments.archive, arguments.stage2_summary)
        added += int(result["events_added"])
    if arguments.stage3_artifact:
        result = ingest_stage3_paths(arguments.archive, arguments.stage3_artifact)
        added += int(result["events_added"])
    if arguments.frontier_artifact:
        result = ingest_frontier_paths(
            arguments.archive,
            arguments.frontier_artifact,
        )
        added += int(result["events_added"])
    summary = _archive_summary(load_archive(arguments.archive), added=added)
    print(json.dumps(summary, sort_keys=True, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())


__all__ = [
    "NEGATIVE_ARCHIVE_KIND",
    "NEGATIVE_ARCHIVE_PATH_ENV",
    "NEGATIVE_ARCHIVE_SCHEMA_VERSION",
    "NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV",
    "NEGATIVE_FEEDBACK_SNAPSHOT_KIND",
    "NEGATIVE_FEEDBACK_SNAPSHOT_SCHEMA_VERSION",
    "NegativeArchiveError",
    "FRONTIER_NEGATIVE_INPUTS_ENV",
    "STAGE2_NEGATIVE_INPUTS_ENV",
    "STAGE3_NEGATIVE_INPUTS_ENV",
    "annotate_rows",
    "configured_stage2_paths",
    "configured_stage3_paths",
    "configured_frontier_paths",
    "feedback_lines",
    "ingest_stage1_rows",
    "ingest_stage2_paths",
    "ingest_stage3_artifact",
    "ingest_stage3_paths",
    "ingest_frontier_paths",
    "load_archive",
    "load_feedback_snapshot_manifest",
    "materialize_feedback_snapshot",
    "resolve_archive_path",
    "resolve_snapshot_path",
]
