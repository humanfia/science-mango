"""Independent, fail-closed exact-distance sidecar for Stage 2 near misses.

The sidecar deliberately has no write path into the Humanize pipeline.  It
harvests only candidates named by completed Stage 2 acknowledgements, replays
their XOR witnesses, and maintains its own durable queue below
``<run-root>/sidecars/stage2-exactification-v1``.

An exact result requires three things:

* a replayed upper-bound witness of weight ``u``;
* one complete first-nonzero-partition UNSAT pass at cutoff ``u - 1`` in both
  CSS sectors; and
* a second, independently checkpointed UNSAT pass over the same partition
  cover.

The first UNSAT pass is retained as ``LOWER_BOUND_PROVEN`` evidence.  A
timeout or solver error is always incomplete; absence of a witness is never
treated as a proof.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import math
import os
import stat
import struct
import time
import uuid
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping


QUEUE_SCHEMA_VERSION = 1
QUEUE_GATE = "qldpc-stage2-exactification-queue"
JOB_GATE = "qldpc-stage2-exactification-job"
RESULT_GATE = "qldpc-stage2-exactification-result"
SIDECAR_NAME = "stage2-exactification-v1"

PENDING = "PENDING"
RUNNING = "RUNNING"
LOWER_BOUND_PROVEN = "LOWER_BOUND_PROVEN"
INCOMPLETE = "INCOMPLETE"
EXACT_DISTANCE_PROVEN = "EXACT_DISTANCE_PROVEN"
ERROR = "ERROR"
RETIRED = "RETIRED"

JOB_STATES = frozenset({
    PENDING,
    RUNNING,
    LOWER_BOUND_PROVEN,
    INCOMPLETE,
    EXACT_DISTANCE_PROVEN,
    ERROR,
    RETIRED,
})
CLAIMABLE_STATES = frozenset({PENDING, INCOMPLETE, ERROR})
OWNED_STATES = frozenset({RUNNING, LOWER_BOUND_PROVEN})


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _stat_identity(metadata: os.stat_result) -> dict[str, int]:
    return {
        "device": int(metadata.st_dev),
        "inode": int(metadata.st_ino),
        "bytes": int(metadata.st_size),
        "mtime_ns": int(metadata.st_mtime_ns),
    }


def _read_regular_json(path: Path, *, label: str) -> tuple[dict[str, Any], str]:
    """Read and hash one stable regular non-symlink JSON object."""

    try:
        before = path.lstat()
    except OSError as exc:
        raise ValueError(f"{label} is unavailable: {path}") from exc
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        raise ValueError(f"{label} must be a regular non-symlink file: {path}")
    try:
        payload = path.read_bytes()
        after = path.lstat()
    except OSError as exc:
        raise ValueError(f"{label} changed while reading: {path}") from exc
    if _stat_identity(before) != _stat_identity(after):
        raise ValueError(f"{label} changed while reading: {path}")
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"{label} is malformed JSON: {path}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain a JSON object: {path}")
    return value, hashlib.sha256(payload).hexdigest()


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            stream.write(_canonical_bytes(dict(value)).decode("utf-8"))
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        try:
            directory_fd = os.open(path.parent, os.O_RDONLY)
        except OSError:
            return
        try:
            os.fsync(directory_fd)
        except OSError:
            pass
        finally:
            os.close(directory_fd)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _write_immutable_json(path: Path, value: Mapping[str, Any]) -> None:
    """Create one content-addressed artifact without any overwrite path."""

    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    payload = _canonical_bytes(dict(value)) + b"\n"
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError:
        existing, _ = _read_regular_json(path, label="immutable exactification result")
        if existing != dict(value):
            raise ValueError("immutable exactification result path collision")
        return
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        try:
            path.unlink()
        except OSError:
            pass
        raise
    try:
        directory_fd = os.open(path.parent, os.O_RDONLY)
    except OSError:
        return
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)


_EXACTIFIER_SOURCE_SHA256 = _file_sha256(Path(__file__).resolve())


def _source_sha256() -> str:
    return _EXACTIFIER_SOURCE_SHA256


def _assert_source_unchanged() -> None:
    if _file_sha256(Path(__file__).resolve()) != _EXACTIFIER_SOURCE_SHA256:
        raise RuntimeError("exactifier source changed after module import")


@dataclass(frozen=True)
class QueueConfig:
    """Core proof policy.  Process and CPU policy belongs to the CLI layer."""

    top_k: int = 13
    timeout_s: float = 300.0
    verification_timeout_s: float | None = None
    workers: int = 1
    seed: int = 0
    solver: str = "auto"
    cardinality_encoding: str = "seqcounter"
    poll_interval_s: float = 30.0
    stale_after_s: float = 900.0
    max_attempts: int = 3
    termination_grace_s: float = 120.0
    retry_backoff_s: float = 60.0
    retry_backoff_max_s: float = 3600.0

    def validate(self) -> "QueueConfig":
        integer_fields = {
            "top_k": self.top_k,
            "workers": self.workers,
            "seed": self.seed,
            "max_attempts": self.max_attempts,
        }
        if any(isinstance(value, bool) or not isinstance(value, int) for value in integer_fields.values()):
            raise ValueError("exactification integer settings must be integers")
        if self.top_k < 1:
            raise ValueError("top_k must be positive")
        if self.workers < 1:
            raise ValueError("workers must be positive")
        if self.max_attempts < 0:
            raise ValueError("max_attempts must be non-negative (zero means unlimited)")
        for name, value in (
            ("timeout_s", self.timeout_s),
            ("poll_interval_s", self.poll_interval_s),
            ("stale_after_s", self.stale_after_s),
            ("termination_grace_s", self.termination_grace_s),
            ("retry_backoff_s", self.retry_backoff_s),
            ("retry_backoff_max_s", self.retry_backoff_max_s),
        ):
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError(f"{name} must be numeric")
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ValueError(f"{name} must be positive and finite")
        if self.verification_timeout_s is not None:
            value = self.verification_timeout_s
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError("verification_timeout_s must be numeric or null")
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ValueError("verification_timeout_s must be positive and finite")
        if not isinstance(self.solver, str) or not self.solver:
            raise ValueError("solver must be a non-empty string")
        if not isinstance(self.cardinality_encoding, str) or not self.cardinality_encoding:
            raise ValueError("cardinality_encoding must be a non-empty string")
        return self

    @classmethod
    def from_json(cls, source: Path | str | Mapping[str, Any]) -> "QueueConfig":
        if isinstance(source, Mapping):
            raw: Any = dict(source)
        else:
            raw, _ = _read_regular_json(Path(source), label="exactification config")
        if not isinstance(raw, Mapping):
            raise ValueError("exactification config must be an object")
        if "queue" in raw:
            raw = raw["queue"]
        if not isinstance(raw, Mapping):
            raise ValueError("exactification config queue must be an object")
        allowed = set(cls.__dataclass_fields__)
        unknown = set(raw) - allowed
        if unknown:
            raise ValueError("unknown exactification queue settings: " + ", ".join(sorted(unknown)))
        return cls(**dict(raw)).validate()

    def as_dict(self) -> dict[str, Any]:
        self.validate()
        return asdict(self)

    @property
    def verify_timeout_s(self) -> float:
        return float(
            self.timeout_s
            if self.verification_timeout_s is None
            else self.verification_timeout_s
        )


@dataclass(frozen=True)
class QueuePaths:
    root: Path
    queue: Path
    lock: Path
    jobs: Path
    results: Path
    checkpoints: Path


def queue_paths(
    run_root: Path | str,
    *,
    state_dir: Path | str | None = None,
) -> QueuePaths:
    root = (
        Path(state_dir)
        if state_dir is not None
        else Path(run_root) / "sidecars" / SIDECAR_NAME
    )
    return QueuePaths(
        root=root,
        queue=root / "queue.json",
        lock=root / "queue.lock",
        jobs=root / "jobs",
        results=root / "results",
        checkpoints=root / "checkpoints",
    )


def _ensure_paths(paths: QueuePaths) -> None:
    paths.root.mkdir(parents=True, exist_ok=True)
    paths.jobs.mkdir(parents=True, exist_ok=True)
    paths.results.mkdir(parents=True, exist_ok=True)
    paths.checkpoints.mkdir(parents=True, exist_ok=True)


def _seal_job(job: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(job)
    value.pop("job_sha256", None)
    value["job_sha256"] = canonical_sha256(value)
    return value


def _validate_job(job: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(job)
    unsigned = dict(value)
    job_sha256 = unsigned.pop("job_sha256", None)
    state = value.get("state")
    if (
        value.get("schema_version") != QUEUE_SCHEMA_VERSION
        or value.get("gate") != JOB_GATE
        or not _is_sha256(value.get("job_id"))
        or value.get("canonical_digest") != value.get("job_id")
        or not _is_sha256(value.get("input_sha256"))
        or state not in JOB_STATES
        or isinstance(value.get("attempts"), bool)
        or not isinstance(value.get("attempts"), int)
        or value.get("attempts") < 0
        or not isinstance(value.get("active"), bool)
        or (
            value.get("next_attempt_at") is not None
            and (
                isinstance(value.get("next_attempt_at"), bool)
                or not isinstance(value.get("next_attempt_at"), (int, float))
                or not math.isfinite(float(value["next_attempt_at"]))
            )
        )
        or not _is_sha256(job_sha256)
        or job_sha256 != canonical_sha256(unsigned)
    ):
        raise ValueError("exactification job seal is invalid")
    if state in OWNED_STATES:
        if (
            not isinstance(value.get("claimed_by"), str)
            or not value.get("claimed_by")
            or not isinstance(value.get("heartbeat_at"), (int, float))
            or not isinstance(value.get("claimed_at"), (int, float))
            or value.get("attempts", 0) < 1
            or not _is_sha256(value.get("proof_job_sha256"))
            or not _is_sha256(value.get("claim_token"))
            or not isinstance(value.get("proof_policy"), Mapping)
            or value.get("proof_policy_sha256")
            != canonical_sha256(value.get("proof_policy"))
        ):
            raise ValueError("owned exactification job lacks a valid claim")
    return value


def _seal_result(result: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(result)
    value.pop("result_sha256", None)
    value["result_sha256"] = canonical_sha256(value)
    return value


def _validate_result(result: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(result)
    unsigned = dict(value)
    digest = unsigned.pop("result_sha256", None)
    if (
        value.get("schema_version") != QUEUE_SCHEMA_VERSION
        or value.get("gate") != RESULT_GATE
        or value.get("status") not in {
            LOWER_BOUND_PROVEN,
            INCOMPLETE,
            EXACT_DISTANCE_PROVEN,
            ERROR,
        }
        or not _is_sha256(value.get("job_id"))
        or not _is_sha256(value.get("input_sha256"))
        or not _is_sha256(value.get("job_sha256"))
        or isinstance(value.get("attempt"), bool)
        or not isinstance(value.get("attempt"), int)
        or value.get("attempt") < 1
        or not isinstance(value.get("claim_worker_id"), str)
        or not value.get("claim_worker_id")
        or not _is_sha256(value.get("claim_token"))
        or not isinstance(value.get("proof_policy"), Mapping)
        or value.get("policy_sha256") != canonical_sha256(value.get("proof_policy"))
        or not _is_sha256(value.get("exactifier_source_sha256"))
        or not _is_sha256(digest)
        or digest != canonical_sha256(unsigned)
    ):
        raise ValueError("exactification result seal is invalid")
    return value


def _seal_queue(queue: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(queue)
    value.pop("queue_sha256", None)
    value["queue_sha256"] = canonical_sha256(value)
    return value


def validate_queue(
    path_or_mapping: Path | str | Mapping[str, Any],
    *,
    expected_source: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if isinstance(path_or_mapping, Mapping):
        value = dict(path_or_mapping)
    else:
        value, _ = _read_regular_json(Path(path_or_mapping), label="exactification queue")
    unsigned = dict(value)
    digest = unsigned.pop("queue_sha256", None)
    jobs = value.get("jobs")
    if (
        value.get("schema_version") != QUEUE_SCHEMA_VERSION
        or value.get("gate") != QUEUE_GATE
        or isinstance(value.get("revision"), bool)
        or not isinstance(value.get("revision"), int)
        or value.get("revision") < 0
        or not isinstance(value.get("source"), Mapping)
        or not isinstance(value.get("config"), Mapping)
        or not isinstance(jobs, list)
        or not _is_sha256(digest)
        or digest != canonical_sha256(unsigned)
    ):
        raise ValueError("exactification queue seal is invalid")
    QueueConfig.from_json(value["config"])
    normalized_jobs = [_validate_job(job) for job in jobs if isinstance(job, Mapping)]
    if len(normalized_jobs) != len(jobs):
        raise ValueError("exactification queue contains a malformed job")
    ids = [job["job_id"] for job in normalized_jobs]
    ranks = [job.get("rank") for job in normalized_jobs if job.get("active")]
    if len(set(ids)) != len(ids):
        raise ValueError("exactification queue contains duplicate jobs")
    if any(isinstance(rank, bool) or not isinstance(rank, int) or rank < 1 for rank in ranks):
        raise ValueError("exactification queue contains an invalid active rank")
    if expected_source is not None and dict(value["source"]) != dict(expected_source):
        raise ValueError("exactification queue source does not match")
    return value


class _QueueLock:
    def __init__(self, paths: QueuePaths) -> None:
        self.paths = paths
        self.stream: Any | None = None

    def __enter__(self) -> "_QueueLock":
        _ensure_paths(self.paths)
        flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        try:
            descriptor = os.open(self.paths.lock, flags, 0o600)
        except OSError as exc:
            raise ValueError("exactification queue lock is unsafe") from exc
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            os.close(descriptor)
            raise ValueError("exactification queue lock must be a regular file")
        self.stream = os.fdopen(descriptor, "a+")
        fcntl.flock(self.stream.fileno(), fcntl.LOCK_EX)
        return self

    def __exit__(self, *_: Any) -> None:
        assert self.stream is not None
        fcntl.flock(self.stream.fileno(), fcntl.LOCK_UN)
        self.stream.close()
        self.stream = None


def _write_job_mirror(paths: QueuePaths, job: Mapping[str, Any]) -> None:
    token = str(job["job_id"])
    _atomic_write_json(paths.jobs / f"{token}.json", dict(job))


def _write_queue(paths: QueuePaths, queue: Mapping[str, Any]) -> dict[str, Any]:
    sealed = _seal_queue(queue)
    validate_queue(sealed)
    for job in sealed["jobs"]:
        _write_job_mirror(paths, job)
    _atomic_write_json(paths.queue, sealed)
    return sealed


def _load_queue(paths: QueuePaths) -> dict[str, Any]:
    return validate_queue(paths.queue)


def _manifest_path(ledger_path: Path) -> Path:
    return ledger_path.with_name(f"{ledger_path.name}.ranked-snapshot.manifest.json")


def _audit_helpers() -> tuple[Any, ...]:
    from scripts.audit_candidate_pool import (
        _construction_candidate,
        _load_ranked_snapshot,
        _stage2_audit_cache_binding,
        safe_digest,
    )
    from scripts.screen_frontier_candidate import build_candidate_code
    from scripts.screen_frontier_xor import (
        load_replayable_sectors,
        verify_bb_translation_symmetry,
    )
    from evaluation.distance_milp import get_code_matrices

    return (
        _construction_candidate,
        _load_ranked_snapshot,
        _stage2_audit_cache_binding,
        safe_digest,
        build_candidate_code,
        load_replayable_sectors,
        verify_bb_translation_symmetry,
        get_code_matrices,
    )


def _validated_stage2_source(ledger_path: Path) -> tuple[dict[str, Any], Any, dict[str, Any]]:
    from evaluation.selection_ledger import (
        snapshot_identity_sha256,
        validate_selection_ledger,
    )

    ledger, ledger_file_sha256 = _read_regular_json(
        ledger_path,
        label="Stage 2 selection ledger",
    )
    ledger_stat = _stat_identity(ledger_path.lstat())
    validated = validate_selection_ledger(
        ledger,
        binding_sha256=str(ledger.get("binding_sha256")),
        snapshot_identity_sha256_value=str(ledger.get("snapshot_identity_sha256")),
        snapshot_rows=ledger.get("snapshot_rows"),  # type: ignore[arg-type]
        eligible_rows=ledger.get("eligible_rows"),  # type: ignore[arg-type]
    )
    manifest, manifest_file_sha256 = _read_regular_json(
        _manifest_path(ledger_path),
        label="Stage 2 ranked snapshot manifest",
    )
    binding = manifest.get("binding")
    if not isinstance(binding, Mapping):
        raise ValueError("Stage 2 ranked snapshot manifest lacks a binding")
    inputs = binding.get("inputs")
    if not isinstance(inputs, list) or any(
        not isinstance(item, Mapping) or not isinstance(item.get("path"), str)
        for item in inputs
    ):
        raise ValueError("Stage 2 ranked snapshot inputs are malformed")
    _, load_snapshot, *_ = _audit_helpers()
    snapshot = load_snapshot(
        ledger_path,
        [Path(str(item["path"])) for item in inputs],
        target_mode=str(binding.get("target_mode")),
    )
    if snapshot is None:
        raise ValueError("Stage 2 ranked snapshot did not validate")
    manifest_after, manifest_after_sha256 = _read_regular_json(
        _manifest_path(ledger_path),
        label="Stage 2 ranked snapshot manifest",
    )
    if (
        snapshot_identity_sha256(snapshot.identity)
        != validated["snapshot_identity_sha256"]
        or snapshot.rows != validated["snapshot_rows"]
        or snapshot.eligible_rows != validated["eligible_rows"]
        or manifest_after != manifest
        or manifest_after_sha256 != manifest_file_sha256
    ):
        raise ValueError("Stage 2 ledger and ranked snapshot identities disagree")
    completed: dict[str, dict[str, Any]] = {}
    for sequence, acknowledgement in enumerate(validated["ack_chain"]):
        if acknowledgement.get("disposition") != "COMPLETED":
            continue
        page = acknowledgement["page"]
        provenance = {
            "sequence": sequence,
            "ack_sha256": acknowledgement["ack_sha256"],
            "page_sha256": page["page_sha256"],
            "previous_ack_sha256": acknowledgement["previous_ack_sha256"],
            "snapshot_identity_sha256": validated["snapshot_identity_sha256"],
            "ledger_binding_sha256": validated["binding_sha256"],
        }
        for item in page["selected_digests"]:
            digest = str(item)
            if digest in completed:
                raise ValueError(
                    "completed Stage 2 acknowledgements contain duplicate digests"
                )
            completed[digest] = provenance
    source = {
        "ledger_path": str(ledger_path.resolve()),
        "ledger_stat": ledger_stat,
        "ledger_file_sha256": ledger_file_sha256,
        "ledger_progress_sha256": validated["progress_sha256"],
        "ledger_last_ack_sha256": validated["last_ack_sha256"],
        "ledger_generation": validated["generation"],
        "ledger_completed_pages": validated["completed_pages"],
        "ledger_cursor": validated["cursor"],
        "completed_ack_pages": sum(
            ack.get("disposition") == "COMPLETED" for ack in validated["ack_chain"]
        ),
        "completed_digests": len(completed),
        "manifest_path": str(_manifest_path(ledger_path).resolve()),
        "manifest_file_sha256": manifest_file_sha256,
        "manifest_sha256": manifest["manifest_sha256"],
        "snapshot_identity": dict(snapshot.identity),
        "snapshot_identity_sha256": validated["snapshot_identity_sha256"],
    }
    return validated, snapshot, {"source": source, "completed": completed}


def _row_digest_candidates(row: Mapping[str, Any]) -> set[str]:
    values: set[str] = set()
    for key in ("triage_identity", "structural_novelty", "novelty"):
        nested = row.get(key)
        if isinstance(nested, Mapping) and _is_sha256(nested.get("canonical_digest")):
            values.add(str(nested["canonical_digest"]))
    if _is_sha256(row.get("canonical_digest")):
        values.add(str(row["canonical_digest"]))
    return values


def _scan_snapshot_prefix(snapshot: Any, stop_index: int, wanted: set[str]) -> dict[str, dict[str, Any]]:
    """Read each relevant snapshot chunk once and authenticate it before JSON."""

    if stop_index < 0 or stop_index > snapshot.eligible_rows:
        raise ValueError("Stage 2 ledger cursor is outside the ranked snapshot")
    if not wanted:
        return {}
    found: dict[str, dict[str, Any]] = {}
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
                raise ValueError("ranked snapshot was replaced before sidecar scan")
            for chunk in snapshot.chunks:
                start_row = int(chunk["start_row"])
                if start_row >= stop_index:
                    break
                end_row = min(int(chunk["end_row"]), stop_index)
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
                count = int(chunk["end_row"]) - start_row + 1
                offsets = struct.unpack(f">{count}Q", encoded_offsets)
                if (
                    offsets[0] != snapshot_start
                    or offsets[-1] != snapshot_end
                    or any(left >= right for left, right in zip(offsets, offsets[1:]))
                ):
                    raise ValueError("ranked snapshot offset chunk is inconsistent")
                for index in range(start_row, end_row):
                    local = index - start_row
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
                    for digest in _row_digest_candidates(row).intersection(wanted):
                        previous = found.get(digest)
                        if previous is not None and _candidate_projection(previous) != _candidate_projection(row):
                            raise ValueError(f"ranked snapshot digest {digest} is ambiguous")
                        found.setdefault(digest, row)
            if (
                _stat_identity(os.fstat(ranked_stream.fileno())) != snapshot.snapshot_stat
                or _stat_identity(os.fstat(offsets_stream.fileno())) != snapshot.offsets_stat
            ):
                raise ValueError("ranked snapshot changed during sidecar scan")
        finally:
            fcntl.flock(offsets_stream.fileno(), fcntl.LOCK_UN)
            fcntl.flock(ranked_stream.fileno(), fcntl.LOCK_UN)
    missing = wanted - set(found)
    if missing:
        example = sorted(missing)[0]
        raise ValueError(
            f"completed Stage 2 digest is absent from its scanned snapshot prefix: {example}"
        )
    return found


_CANDIDATE_PROJECTION_FIELDS = (
    "ansatz",
    "geometry",
    "construction",
    "ell",
    "m",
    "A_terms",
    "B_terms",
    "C_terms",
    "D_terms",
    "n",
    "k",
    "required_distance",
    "target_mode",
    "target",
)


def _candidate_projection(candidate: Mapping[str, Any]) -> dict[str, Any]:
    return {
        name: candidate[name]
        for name in _CANDIDATE_PROJECTION_FIELDS
        if name in candidate and candidate[name] is not None
    }


def _advisory_upper(artifact: Mapping[str, Any]) -> int | None:
    objectives: list[int] = []
    for sector in artifact.get("sectors", []):
        if not isinstance(sector, Mapping) or sector.get("operator") is None:
            continue
        objective = sector.get("objective")
        if isinstance(objective, bool) or not isinstance(objective, int) or objective < 1:
            continue
        objectives.append(objective)
    return min(objectives) if objectives else None


def _matrix_dimensions(candidate: Mapping[str, Any]) -> tuple[int, int]:
    *_, build_candidate_code, _, _, get_code_matrices = _audit_helpers()
    import numpy as np

    code = build_candidate_code(dict(candidate))
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1 for value in get_code_matrices(code)
    )
    n = int(hx.shape[1])
    if hz.shape[1] != n or lx.shape[1] != n or lz.shape[1] != n:
        raise ValueError("candidate CSS matrices have inconsistent widths")
    k = int(lx.shape[0])
    if int(lz.shape[0]) != k or k < 1:
        raise ValueError("candidate CSS logical matrices have inconsistent ranks")
    return n, k


def _full_replay_advisory(
    item: Mapping[str, Any],
    *,
    replay_loader: Callable[..., Any] | None,
) -> dict[str, Any] | None:
    (
        _,
        _,
        cache_binding_builder,
        _,
        _,
        default_replay_loader,
        symmetry_verifier,
        _,
    ) = _audit_helpers()
    artifact_path = Path(str(item["artifact_path"]))
    artifact, artifact_sha256 = _read_regular_json(artifact_path, label="Stage 2 XOR artifact")
    if artifact_sha256 != item.get("advisory_artifact_sha256"):
        return None
    candidate = artifact.get("candidate")
    if not isinstance(candidate, Mapping):
        return None
    candidate = dict(candidate)
    digest = str(item["canonical_digest"])
    if candidate.get("canonical_digest") != digest:
        return None
    if _candidate_projection(candidate) != dict(item["candidate_projection"]):
        return None
    try:
        symmetry = symmetry_verifier(candidate)
        if not isinstance(symmetry, Mapping) or symmetry.get("verified") is not True:
            return None
        cache_binding = cache_binding_builder(candidate, symmetry)
        loader = default_replay_loader if replay_loader is None else replay_loader
        sectors = loader(
            artifact_path,
            candidate,
            threshold_only=True,
            translation_symmetry=dict(symmetry),
            expected_cache_binding=cache_binding,
        )
        witnesses = [
            dict(sector)
            for sector in sectors
            if (
                isinstance(sector, Mapping)
                and sector.get("operator") is not None
                and sector.get("witness_verified") is True
                and isinstance(sector.get("objective"), int)
                and not isinstance(sector.get("objective"), bool)
                and int(sector["objective"]) >= 1
            )
        ]
        if not witnesses:
            return None
        upper = min(int(witness["objective"]) for witness in witnesses)
        upper_witness = min(
            (witness for witness in witnesses if int(witness["objective"]) == upper),
            key=lambda witness: str(witness.get("sector")),
        )
        n, k = _matrix_dimensions(candidate)
    except (ImportError, KeyError, OSError, TypeError, ValueError):
        return None
    if (
        candidate.get("n") != n
        or candidate.get("k") != k
        or upper >= int(candidate.get("required_distance", 0))
    ):
        return None
    score = Fraction(k * upper * upper, n)
    input_payload = {
        "canonical_digest": digest,
        "candidate": candidate,
        "artifact_path": str(artifact_path.resolve()),
        "artifact_sha256": artifact_sha256,
        "translation_symmetry": dict(symmetry),
        "cache_binding": cache_binding,
        "selection_ack": dict(item["selection_ack"]),
        "initial_upper_bound": upper,
        "initial_upper_witness": upper_witness,
        "n": n,
        "k": k,
    }
    return {
        **input_payload,
        "input_sha256": canonical_sha256(input_payload),
        "score": {
            "numerator": score.numerator,
            "denominator": score.denominator,
            "decimal": float(score),
        },
    }


def _discover_jobs(
    *,
    ledger_path: Path,
    stage2_state_dir: Path,
    config: QueueConfig,
    replay_loader: Callable[..., Any] | None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    validated, snapshot, source_data = _validated_stage2_source(ledger_path)
    completed = dict(source_data["completed"])
    construction_candidate, _, _, safe_digest, *_ = _audit_helpers()

    advisory: list[dict[str, Any]] = []
    for digest in sorted(completed):
        artifact_path = stage2_state_dir / "xor" / f"{safe_digest(digest)}.json"
        if not artifact_path.exists():
            continue
        try:
            artifact, artifact_sha256 = _read_regular_json(
                artifact_path,
                label="Stage 2 XOR artifact",
            )
        except ValueError:
            continue
        upper = _advisory_upper(artifact)
        raw_candidate = artifact.get("candidate")
        if upper is None or not isinstance(raw_candidate, Mapping):
            continue
        if raw_candidate.get("canonical_digest") != digest:
            continue
        n = raw_candidate.get("n")
        k = raw_candidate.get("k")
        if (
            isinstance(n, bool)
            or not isinstance(n, int)
            or n < 1
            or isinstance(k, bool)
            or not isinstance(k, int)
            or k < 1
        ):
            continue
        advisory.append({
            "canonical_digest": digest,
            "artifact_path": str(artifact_path),
            "advisory_artifact_sha256": artifact_sha256,
            "candidate_projection": _candidate_projection(raw_candidate),
            "selection_ack": completed[digest],
            "advisory_upper_bound": upper,
            "advisory_score": Fraction(k * upper * upper, n),
        })
    wanted = {str(item["canonical_digest"]) for item in advisory}
    rows = _scan_snapshot_prefix(snapshot, int(validated["cursor"]), wanted)
    authenticated: list[dict[str, Any]] = []
    for item in advisory:
        digest = str(item["canonical_digest"])
        try:
            snapshot_candidate = construction_candidate(rows[digest], digest)
        except (KeyError, TypeError, ValueError):
            continue
        if _candidate_projection(snapshot_candidate) != item["candidate_projection"]:
            continue
        authenticated.append(item)
    advisory = authenticated
    advisory.sort(key=lambda item: (-item["advisory_score"], item["canonical_digest"]))

    # Raw scores only schedule work.  Fully replay every possible winner and
    # every raw tie at the current K boundary; invalid entries extend the scan.
    replayed: list[dict[str, Any]] = []
    replay_attempts = 0
    for item in advisory:
        if len(replayed) >= config.top_k:
            ordered = sorted(
                replayed,
                key=lambda value: (
                    -Fraction(value["score"]["numerator"], value["score"]["denominator"]),
                    value["canonical_digest"],
                ),
            )
            boundary = Fraction(
                ordered[config.top_k - 1]["score"]["numerator"],
                ordered[config.top_k - 1]["score"]["denominator"],
            )
            if item["advisory_score"] < boundary:
                break
        replay_attempts += 1
        result = _full_replay_advisory(item, replay_loader=replay_loader)
        if result is not None:
            replayed.append(result)
    replayed.sort(
        key=lambda item: (
            -Fraction(item["score"]["numerator"], item["score"]["denominator"]),
            item["canonical_digest"],
        )
    )
    if len(replayed) > config.top_k:
        boundary = Fraction(
            replayed[config.top_k - 1]["score"]["numerator"],
            replayed[config.top_k - 1]["score"]["denominator"],
        )
        replayed = [
            item
            for item in replayed
            if Fraction(item["score"]["numerator"], item["score"]["denominator"])
            >= boundary
        ]
    source = {
        **source_data["source"],
        "stage2_state_dir": str(stage2_state_dir.resolve()),
        "advisory_artifacts": len(advisory),
        "replay_attempts": replay_attempts,
        "selected_replay_valid_artifacts": len(replayed),
        "discovery_policy": {
            "method": "raw-advisory-boundary-then-full-replay-v1",
            "raw_boundary_ties_replayed": True,
            "caveat": (
                "artifacts below the raw score boundary are not fully replayed; "
                "raw JSON is scheduling advice, never exact-distance evidence"
            ),
        },
    }
    return source, replayed

def _new_job(item: Mapping[str, Any], *, rank: int, now: float) -> dict[str, Any]:
    return _seal_job({
        "schema_version": QUEUE_SCHEMA_VERSION,
        "gate": JOB_GATE,
        "job_id": item["canonical_digest"],
        "canonical_digest": item["canonical_digest"],
        "input_sha256": item["input_sha256"],
        "input": {
            key: item[key]
            for key in (
                "candidate",
                "artifact_path",
                "artifact_sha256",
                "translation_symmetry",
                "cache_binding",
                "selection_ack",
                "initial_upper_bound",
                "initial_upper_witness",
                "n",
                "k",
                "score",
            )
        },
        "rank": rank,
        "active": True,
        "state": PENDING,
        "attempts": 0,
        "created_at": now,
        "updated_at": now,
        "claimed_by": None,
        "claimed_at": None,
        "heartbeat_at": None,
        "result_path": None,
        "last_error": None,
        "next_attempt_at": None,
        "claim_token": None,
    })


def _cached_refresh_if_unchanged(
    paths: QueuePaths,
    *,
    ledger_path: Path,
    stage2_state_dir: Path,
    config: QueueConfig,
) -> dict[str, Any] | None:
    """Cheap worker-poll no-op keyed by the ledger's atomic file identity."""

    if not paths.queue.exists():
        return None
    try:
        current_stat = _stat_identity(ledger_path.lstat())
    except OSError:
        return None
    with _QueueLock(paths):
        queue = _load_queue(paths)
        source = queue["source"]
        if (
            queue.get("config") == config.as_dict()
            and source.get("ledger_path") == str(ledger_path.resolve())
            and source.get("ledger_stat") == current_stat
            and source.get("stage2_state_dir") == str(stage2_state_dir.resolve())
        ):
            return queue
    return None


def _reject_source_rollback(
    previous: Mapping[str, Any],
    discovered: Mapping[str, Any],
) -> None:
    fields = ("ledger_generation", "ledger_completed_pages", "ledger_cursor")
    if not all(isinstance(previous.get(field), int) for field in fields):
        return
    old_position = tuple(int(previous[field]) for field in fields)
    new_position = tuple(int(discovered.get(field, -1)) for field in fields)
    if new_position < old_position:
        raise ValueError("exactification refresh would roll Stage 2 progress back")
    if new_position == old_position and (
        discovered.get("ledger_last_ack_sha256")
        != previous.get("ledger_last_ack_sha256")
        or discovered.get("ledger_progress_sha256")
        != previous.get("ledger_progress_sha256")
    ):
        raise ValueError("equal Stage 2 progress has conflicting ACK evidence")


def refresh_queue(
    *,
    ledger_path: Path | str,
    stage2_state_dir: Path | str,
    run_root: Path | str | None = None,
    state_dir: Path | str | None = None,
    config: QueueConfig = QueueConfig(),
    replay_loader: Callable[..., Any] | None = None,
    now: float | None = None,
) -> dict[str, Any]:
    """Harvest completed Stage 2 near misses without accepting stale discovery."""

    config = config.validate()
    if run_root is None and state_dir is None:
        raise ValueError("refresh_queue requires run_root or state_dir")
    paths = queue_paths(Path(".") if run_root is None else run_root, state_dir=state_dir)
    _ensure_paths(paths)
    ledger_path = Path(ledger_path)
    stage2_state_dir = Path(stage2_state_dir)
    cached = _cached_refresh_if_unchanged(
        paths,
        ledger_path=ledger_path,
        stage2_state_dir=stage2_state_dir,
        config=config,
    )
    if cached is not None:
        return cached

    for _discovery_attempt in range(3):
        timestamp = time.time() if now is None else float(now)
        source, items = _discover_jobs(
            ledger_path=ledger_path,
            stage2_state_dir=stage2_state_dir,
            config=config,
            replay_loader=replay_loader,
        )
        with _QueueLock(paths):
            try:
                current_ledger_stat = _stat_identity(ledger_path.lstat())
            except OSError:
                continue
            if current_ledger_stat != source.get("ledger_stat"):
                continue
            if paths.queue.exists():
                previous = _load_queue(paths)
                _reject_source_rollback(previous["source"], source)
                previous_jobs = {
                    job["job_id"]: dict(job) for job in previous["jobs"]
                }
                revision = int(previous["revision"]) + 1
                created_at = previous["created_at"]
            else:
                previous_jobs = {}
                revision = 0
                created_at = timestamp

            jobs: list[dict[str, Any]] = []
            active_ids: set[str] = set()
            for rank, item in enumerate(items, start=1):
                job_id = str(item["canonical_digest"])
                active_ids.add(job_id)
                old = previous_jobs.get(job_id)
                if old is not None and old.get("state") in OWNED_STATES:
                    updated = dict(old)
                    updated.update({
                        "rank": rank,
                        "active": True,
                        "updated_at": timestamp,
                    })
                    updated.pop("retirement_pending", None)
                    if old.get("input_sha256") != item["input_sha256"]:
                        updated["refresh_pending_input_sha256"] = item["input_sha256"]
                    jobs.append(_seal_job(updated))
                    continue
                if old is not None and old.get("input_sha256") == item["input_sha256"]:
                    updated = dict(old)
                    updated.update({
                        "rank": rank,
                        "active": True,
                        "updated_at": timestamp,
                    })
                    if old.get("state") == RETIRED:
                        restored = old.get(
                            "terminal_result_state",
                            old.get("retired_from_state", PENDING),
                        )
                        if restored in OWNED_STATES or restored == RETIRED:
                            restored = PENDING
                        updated["state"] = restored
                        updated.pop("retirement_pending", None)
                        updated.pop("retired_from_state", None)
                        updated.pop("terminal_result_state", None)
                    jobs.append(_seal_job(updated))
                    continue
                jobs.append(_new_job(item, rank=rank, now=timestamp))

            for job_id, old in previous_jobs.items():
                if job_id in active_ids:
                    continue
                retired = dict(old)
                retired.update({
                    "active": False,
                    "rank": None,
                    "retired_from_state": old.get("retired_from_state", old["state"]),
                    "updated_at": timestamp,
                })
                if old["state"] not in OWNED_STATES:
                    retired.update({
                        "state": RETIRED,
                        "claimed_by": None,
                        "claimed_at": None,
                        "heartbeat_at": None,
                    })
                else:
                    retired["retirement_pending"] = True
                jobs.append(_seal_job(retired))
            jobs.sort(key=lambda job: (
                not job["active"],
                job.get("rank") or 10**18,
                job["job_id"],
            ))
            queue = {
                "schema_version": QUEUE_SCHEMA_VERSION,
                "gate": QUEUE_GATE,
                "revision": revision,
                "created_at": created_at,
                "updated_at": timestamp,
                "producer": {"source_sha256": _source_sha256()},
                "source": source,
                "config": config.as_dict(),
                "jobs": jobs,
            }
            return _write_queue(paths, queue)
    raise RuntimeError("Stage 2 ledger changed during three exactification refresh attempts")

def _recover_stale_in_memory(queue: dict[str, Any], config: QueueConfig, now: float) -> bool:
    changed = False
    jobs: list[dict[str, Any]] = []
    for raw in queue["jobs"]:
        job = dict(raw)
        heartbeat = job.get("heartbeat_at")
        stale = (
            job.get("state") in OWNED_STATES
            and isinstance(heartbeat, (int, float))
            and now - float(heartbeat) >= float(config.stale_after_s)
        )
        if stale:
            job.update({
                "state": PENDING,
                "claimed_by": None,
                "claimed_at": None,
                "heartbeat_at": None,
                "updated_at": now,
                "last_error": "stale claim recovered",
                "next_attempt_at": now,
                "claim_token": None,
            })
            changed = True
        jobs.append(_seal_job(job) if stale else raw)
    if changed:
        queue["jobs"] = jobs
    return changed


def recover_stale_jobs(
    paths: QueuePaths,
    config: QueueConfig = QueueConfig(),
    *,
    now: float | None = None,
) -> dict[str, Any]:
    config = config.validate()
    timestamp = time.time() if now is None else float(now)
    with _QueueLock(paths):
        queue = _load_queue(paths)
        if _recover_stale_in_memory(queue, config, timestamp):
            queue.update({"revision": int(queue["revision"]) + 1, "updated_at": timestamp})
            return _write_queue(paths, queue)
        return queue


def claim_next_job(
    paths: QueuePaths,
    *,
    worker_id: str,
    config: QueueConfig = QueueConfig(),
    now: float | None = None,
) -> dict[str, Any] | None:
    config = config.validate()
    if not isinstance(worker_id, str) or not worker_id:
        raise ValueError("worker_id must be a non-empty string")
    timestamp = time.time() if now is None else float(now)
    with _QueueLock(paths):
        queue = _load_queue(paths)
        changed = _recover_stale_in_memory(queue, config, timestamp)
        candidates = [
            job
            for job in queue["jobs"]
            if (
                job["active"]
                and job["state"] in CLAIMABLE_STATES
                and (
                    job.get("next_attempt_at") is None
                    or float(job["next_attempt_at"]) <= timestamp
                )
                and (config.max_attempts == 0 or job["attempts"] < config.max_attempts)
            )
        ]
        candidates.sort(
            key=lambda job: (job["attempts"], job["rank"], job["job_id"]),
        )
        claimed: dict[str, Any] | None = None
        if candidates:
            target = candidates[0]["job_id"]
            updated_jobs = []
            for raw in queue["jobs"]:
                job = dict(raw)
                if job["job_id"] == target:
                    claim_policy = config.as_dict()
                    claim_policy_sha256 = canonical_sha256(claim_policy)
                    if not _is_sha256(job.get("proof_job_sha256")):
                        job["proof_job_sha256"] = job["job_sha256"]
                        job["proof_policy"] = claim_policy
                        job["proof_policy_sha256"] = claim_policy_sha256
                    elif (
                        job.get("proof_policy") != claim_policy
                        or job.get("proof_policy_sha256") != claim_policy_sha256
                    ):
                        raise ValueError(
                            "claim policy differs from the job's immutable proof policy"
                        )
                    next_attempt = int(job["attempts"]) + 1
                    claim_token = canonical_sha256({
                        "gate": "qldpc-stage2-exactification-claim",
                        "job_id": job["job_id"],
                        "proof_job_sha256": job["proof_job_sha256"],
                        "proof_policy_sha256": job["proof_policy_sha256"],
                        "attempt": next_attempt,
                        "worker_id": worker_id,
                        "claimed_at": timestamp,
                        "nonce": uuid.uuid4().hex,
                    })
                    job.update({
                        "state": RUNNING,
                        "attempts": next_attempt,
                        "claim_token": claim_token,
                        "claimed_by": worker_id,
                        "claimed_at": timestamp,
                        "heartbeat_at": timestamp,
                        "updated_at": timestamp,
                        "last_error": None,
                        "next_attempt_at": None,
                    })
                    job = _seal_job(job)
                    claimed = job
                updated_jobs.append(job)
            queue["jobs"] = updated_jobs
            changed = True
        if changed:
            queue.update({"revision": int(queue["revision"]) + 1, "updated_at": timestamp})
            _write_queue(paths, queue)
        return claimed


def _update_claim(
    paths: QueuePaths,
    *,
    job_id: str,
    worker_id: str,
    attempt: int,
    claim_token: str,
    state: str = RUNNING,
    now: float | None = None,
) -> None:
    timestamp = time.time() if now is None else float(now)
    with _QueueLock(paths):
        queue = _load_queue(paths)
        changed = False
        jobs = []
        for raw in queue["jobs"]:
            job = dict(raw)
            if job["job_id"] == job_id:
                if (
                    job.get("claimed_by") != worker_id
                    or job.get("state") not in OWNED_STATES
                    or job.get("attempts") != attempt
                    or job.get("claim_token") != claim_token
                ):
                    raise ValueError("exactification job claim was lost")
                job.update({"state": state, "heartbeat_at": timestamp, "updated_at": timestamp})
                job = _seal_job(job)
                changed = True
            jobs.append(job)
        if not changed:
            raise ValueError("exactification job is absent from queue")
        queue["jobs"] = jobs
        queue.update({"revision": int(queue["revision"]) + 1, "updated_at": timestamp})
        _write_queue(paths, queue)


def _load_job_input(
    job: Mapping[str, Any],
    replay_loader: Callable[..., Any] | None,
) -> tuple[dict[str, Any], tuple[Any, Any, Any, Any], int, dict[str, Any]]:
    """Re-read and replay the upper witness at proof time."""

    candidate_input = job.get("input")
    if not isinstance(candidate_input, Mapping):
        raise ValueError("exactification job lacks bound input")
    candidate = candidate_input.get("candidate")
    if not isinstance(candidate, Mapping):
        raise ValueError("exactification job candidate is malformed")
    candidate = dict(candidate)
    artifact_path = Path(str(candidate_input.get("artifact_path")))
    artifact, artifact_sha256 = _read_regular_json(artifact_path, label="Stage 2 XOR artifact")
    if artifact_sha256 != candidate_input.get("artifact_sha256"):
        raise ValueError("Stage 2 XOR artifact changed after queueing")
    if artifact.get("candidate") != candidate:
        raise ValueError("Stage 2 XOR artifact candidate changed after queueing")
    (
        _,
        _,
        cache_binding_builder,
        _,
        build_candidate_code,
        default_replay_loader,
        symmetry_verifier,
        get_code_matrices,
    ) = _audit_helpers()
    symmetry = symmetry_verifier(candidate)
    cache_binding = cache_binding_builder(candidate, symmetry)
    if (
        symmetry != candidate_input.get("translation_symmetry")
        or cache_binding != candidate_input.get("cache_binding")
    ):
        raise ValueError("Stage 2 upper-bound replay binding changed")
    loader = default_replay_loader if replay_loader is None else replay_loader
    sectors = loader(
        artifact_path,
        candidate,
        threshold_only=True,
        translation_symmetry=symmetry,
        expected_cache_binding=cache_binding,
    )
    witnesses = [
        dict(item)
        for item in sectors
        if (
            isinstance(item, Mapping)
            and item.get("operator") is not None
            and item.get("witness_verified") is True
            and isinstance(item.get("objective"), int)
            and not isinstance(item.get("objective"), bool)
            and int(item["objective"]) >= 1
        )
    ]
    if not witnesses:
        raise ValueError("Stage 2 upper-bound witness no longer replays")
    upper = min(int(item["objective"]) for item in witnesses)
    witness = min(
        (item for item in witnesses if int(item["objective"]) == upper),
        key=lambda item: str(item.get("sector")),
    )
    if upper != candidate_input.get("initial_upper_bound"):
        raise ValueError("Stage 2 upper bound changed after queueing")
    import numpy as np

    code = build_candidate_code(candidate)
    matrices = tuple(
        np.asarray(value, dtype=np.uint8) & 1 for value in get_code_matrices(code)
    )
    hx, hz, lx, lz = matrices
    if (
        hx.shape[1] != candidate_input.get("n")
        or hz.shape[1] != candidate_input.get("n")
        or lx.shape[0] != candidate_input.get("k")
        or lz.shape[0] != candidate_input.get("k")
    ):
        raise ValueError("exactification matrices changed after queueing")
    return candidate, matrices, upper, {
        "kind": "stage2-xor-replayed-witness",
        "artifact_sha256": artifact_sha256,
        "sector_evidence": witness,
    }


def _validate_solver_evidence(
    evidence: Mapping[str, Any],
    checks: Any,
    logicals: Any,
    *,
    cutoff: int,
    sector: str,
    partition: int,
    encoding: str,
    checkpoint_identity: Mapping[str, Any],
) -> None:
    """Replay the exact typed SAT instance; a bare UNSAT hash is insufficient."""

    digest = evidence.get("evidence_sha256")
    unsigned = dict(evidence)
    unsigned.pop("evidence_sha256", None)
    if not _is_sha256(digest) or digest != canonical_sha256(unsigned):
        raise ValueError("SAT solver evidence seal is invalid")
    outcome = str(evidence.get("outcome", "")).lower()
    if outcome not in {"sat", "unsat"}:
        return

    from evaluation import distance_sat

    backend = evidence.get("backend")
    solver_name = backend.get("solver") if isinstance(backend, Mapping) else None
    if not isinstance(solver_name, str) or not solver_name or solver_name == "auto":
        raise ValueError("terminal SAT evidence lacks a concrete backend")
    expected_instance = distance_sat._instance_binding(
        checks,
        logicals,
        max_weight=cutoff,
        sector=sector,
        encoding=encoding,
        solver_name=solver_name,
        checkpoint_identity=checkpoint_identity,
        partition_index=partition,
        anchor_indices=(),
    )
    expected_instance["native_thread_environment"] = (
        distance_sat.enforce_sat_native_thread_budget()
    )
    expected_instance["binding_sha256"] = canonical_sha256({
        key: value
        for key, value in expected_instance.items()
        if key != "binding_sha256"
    })
    if (
        evidence.get("schema_version") != distance_sat.SAT_EVIDENCE_SCHEMA_VERSION
        or evidence.get("evidence_kind") != distance_sat.SAT_EVIDENCE_KIND
        or evidence.get("formulation") != distance_sat.SAT_FORMULATION
        or evidence.get("sector") != sector
        or evidence.get("max_weight") != cutoff
        or evidence.get("partition_index") != partition
        or evidence.get("cardinality_encoding") != encoding
        or evidence.get("anchor_indices") != []
        or evidence.get("zero_anchor_indices") != []
        or evidence.get("one_anchor_index") is not None
        or evidence.get("anchor_cube_sha256") is not None
        or evidence.get("backend") != expected_instance["backend"]
        or evidence.get("instance") != expected_instance
    ):
        raise ValueError("SAT solver evidence is not bound to the requested unit")

def _solver_outcome(evidence: Mapping[str, Any]) -> str:
    return str(evidence.get("outcome", "")).lower()


def _result_base(
    job: Mapping[str, Any],
    *,
    status: str,
    started_at: float,
    now: float,
    lower_bound: int,
    upper_bound: int,
    upper_witness: Mapping[str, Any],
    iterations: list[dict[str, Any]],
    reason: str | None = None,
) -> dict[str, Any]:
    policy = job.get("_proof_policy")
    if not isinstance(policy, Mapping):
        raise ValueError("exactification result lacks its proof policy")
    value = {
        "schema_version": QUEUE_SCHEMA_VERSION,
        "gate": RESULT_GATE,
        "status": status,
        "job_id": job["job_id"],
        "canonical_digest": job["canonical_digest"],
        "input_sha256": job["input_sha256"],
        "job_sha256": job.get("proof_job_sha256", job["job_sha256"]),
        "attempt": job["attempts"],
        "claim_worker_id": job["claimed_by"],
        "claim_token": job["claim_token"],
        "proof_policy": dict(policy),
        "policy_sha256": canonical_sha256(policy),
        "exactifier_source_sha256": _source_sha256(),
        "started_at": started_at,
        "updated_at": now,
        "elapsed_s": max(0.0, now - started_at),
        "bounds": {"lower": lower_bound, "upper": upper_bound},
        "upper_witness": dict(upper_witness),
        "iterations": iterations,
        "exact_distance": upper_bound if status == EXACT_DISTANCE_PROVEN else None,
        "publication_certificate": False,
        "pipeline_promotion": False,
        "reason": reason,
    }
    return _seal_result(value)


def _result_artifact_path(
    paths: QueuePaths,
    result: Mapping[str, Any],
    *,
    disposition: str,
) -> Path:
    if disposition not in {"provisional", "accepted", "stale"}:
        raise ValueError("unknown exactification result disposition")
    return (
        paths.results
        / disposition
        / str(result["job_id"])
        / f"attempt-{int(result['attempt']):03d}-{result['result_sha256']}.json"
    )

def _write_provisional_result(paths: QueuePaths, result: Mapping[str, Any]) -> Path:
    validated = _validate_result(result)
    path = _result_artifact_path(
        paths,
        validated,
        disposition="provisional",
    )
    _write_immutable_json(path, validated)
    return path


def exactify_job(
    job: Mapping[str, Any],
    *,
    paths: QueuePaths,
    config: QueueConfig = QueueConfig(),
    solve_fn: Callable[..., Mapping[str, Any]] | None = None,
    replay_loader: Callable[..., Any] | None = None,
    now: Callable[[], float] | float | None = None,
    cancel_event: Any | None = None,
) -> dict[str, Any]:
    """Run one exactification job without mutating any Stage 2 artifact."""

    config = config.validate()
    _assert_source_unchanged()
    job = _validate_job(job)
    requested_policy = config.as_dict()
    if (
        job.get("proof_policy") != requested_policy
        or job.get("proof_policy_sha256") != canonical_sha256(requested_policy)
    ):
        raise ValueError("exactification config differs from the claimed proof policy")
    job = {**job, "_proof_policy": dict(job["proof_policy"])}
    if job["state"] not in OWNED_STATES:
        raise ValueError("exactification requires a claimed job")
    worker_id = str(job["claimed_by"])
    clock: Callable[[], float]
    if callable(now):
        clock = now
    elif now is None:
        clock = time.time
    else:
        fixed = float(now)
        clock = lambda: fixed
    started_at = clock()
    _ensure_paths(paths)
    try:
        candidate, (hx, hz, lx, lz), upper, upper_witness = _load_job_input(
            job,
            replay_loader,
        )
    except (ImportError, KeyError, OSError, TypeError, ValueError) as exc:
        result = _result_base(
            job,
            status=ERROR,
            started_at=started_at,
            now=clock(),
            lower_bound=1,
            upper_bound=int(job["input"].get("initial_upper_bound", 1)),
            upper_witness={},
            iterations=[],
            reason=f"upper-bound replay failed: {exc}",
        )
        _write_provisional_result(paths, result)
        return result

    if solve_fn is None:
        from evaluation.distance_sat import solve_css_sector_sat

        solve_fn = solve_css_sector_sat
    from evaluation.distance_sat import css_sector_matrices, verify_css_threshold_sat_witness

    lower_bound = 1
    iterations: list[dict[str, Any]] = []
    iteration_number = 0
    while True:
        if upper <= 1:
            result = _result_base(
                job,
                status=EXACT_DISTANCE_PROVEN,
                started_at=started_at,
                now=clock(),
                lower_bound=upper,
                upper_bound=upper,
                upper_witness=upper_witness,
                iterations=iterations,
            )
            _write_provisional_result(paths, result)
            return result
        iteration_number += 1
        cutoff = upper - 1
        iteration: dict[str, Any] = {
            "iteration": iteration_number,
            "upper_bound": upper,
            "cutoff": cutoff,
            "passes": {},
        }
        restart = False
        for pass_name in ("build", "verify"):
            pass_evidence: list[dict[str, Any]] = []
            timeout = config.timeout_s if pass_name == "build" else config.verify_timeout_s
            for sector in ("X", "Z"):
                checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
                for partition in range(int(logicals.shape[0])):
                    if cancel_event is not None and cancel_event.is_set():
                        iteration["passes"][pass_name] = pass_evidence
                        iterations.append(iteration)
                        result = _result_base(
                            job,
                            status=INCOMPLETE,
                            started_at=started_at,
                            now=clock(),
                            lower_bound=lower_bound,
                            upper_bound=upper,
                            upper_witness=upper_witness,
                            iterations=iterations,
                            reason="cancelled",
                        )
                        _write_provisional_result(paths, result)
                        return result
                    identity = {
                        "schema_version": 1,
                        "gate": "qldpc-stage2-exactification-sat-unit",
                        "job_id": job["job_id"],
                        "input_sha256": job["input_sha256"],
                        "job_sha256": job.get(
                            "proof_job_sha256", job["job_sha256"],
                        ),
                        "policy_sha256": canonical_sha256(config.as_dict()),
                        "exactifier_source_sha256": _source_sha256(),
                        "iteration": iteration_number,
                        "pass": pass_name,
                        "upper_bound": upper,
                        "cutoff": cutoff,
                        "sector": sector,
                        "partition_index": partition,
                        "solver": config.solver,
                        "cardinality_encoding": config.cardinality_encoding,
                    }
                    checkpoint = (
                        paths.checkpoints
                        / job["job_id"]
                        / f"u{upper}"
                        / f"{pass_name}-{sector}-{partition}.json"
                    )
                    _assert_source_unchanged()
                    evidence = dict(solve_fn(
                        checks,
                        logicals,
                        max_weight=cutoff,
                        timeout=float(timeout),
                        workers=config.workers,
                        seed=config.seed,
                        partition_index=partition,
                        sector=sector,
                        cardinality_encoding=config.cardinality_encoding,
                        solver=config.solver,
                        checkpoint_path=checkpoint,
                        resume=True,
                        checkpoint_identity=identity,
                        cancel_event=cancel_event,
                        termination_grace_s=float(config.termination_grace_s),
                    ))
                    try:
                        _validate_solver_evidence(
                            evidence,
                            checks,
                            logicals,
                            cutoff=cutoff,
                            sector=sector,
                            partition=partition,
                            encoding=config.cardinality_encoding,
                            checkpoint_identity=identity,
                        )
                    except ValueError as exc:
                        iteration["passes"][pass_name] = pass_evidence + [evidence]
                        iterations.append(iteration)
                        result = _result_base(
                            job,
                            status=ERROR,
                            started_at=started_at,
                            now=clock(),
                            lower_bound=lower_bound,
                            upper_bound=upper,
                            upper_witness=upper_witness,
                            iterations=iterations,
                            reason=str(exc),
                        )
                        _write_provisional_result(paths, result)
                        return result
                    pass_evidence.append(evidence)
                    _update_claim(
                        paths,
                        job_id=job["job_id"],
                        worker_id=worker_id,
                        attempt=int(job["attempts"]),
                        claim_token=str(job["claim_token"]),
                        state=RUNNING,
                    )
                    outcome = _solver_outcome(evidence)
                    if outcome == "sat":
                        failures = verify_css_threshold_sat_witness(evidence, checks, logicals)
                        objective = evidence.get("objective")
                        if (
                            failures
                            or isinstance(objective, bool)
                            or not isinstance(objective, int)
                            or not 1 <= objective <= cutoff
                        ):
                            iteration["passes"][pass_name] = pass_evidence
                            iterations.append(iteration)
                            result = _result_base(
                                job,
                                status=ERROR,
                                started_at=started_at,
                                now=clock(),
                                lower_bound=lower_bound,
                                upper_bound=upper,
                                upper_witness=upper_witness,
                                iterations=iterations,
                                reason="SAT witness failed replay: " + "; ".join(failures),
                            )
                            _write_provisional_result(paths, result)
                            return result
                        if pass_name == "verify":
                            iteration["passes"][pass_name] = pass_evidence
                            iteration["verification_contradiction"] = {
                                "sector": sector,
                                "partition_index": partition,
                                "witness_evidence_sha256": evidence["evidence_sha256"],
                            }
                            iterations.append(iteration)
                            result = _result_base(
                                job,
                                status=ERROR,
                                started_at=started_at,
                                now=clock(),
                                lower_bound=lower_bound,
                                upper_bound=upper,
                                upper_witness=upper_witness,
                                iterations=iterations,
                                reason=(
                                    "verification SAT witness contradicts the build "
                                    "UNSAT pass"
                                ),
                            )
                            _write_provisional_result(paths, result)
                            return result
                        upper = int(objective)
                        lower_bound = 1
                        upper_witness = {
                            "kind": "partitioned-sat-replayed-witness",
                            "pass": pass_name,
                            "sector": sector,
                            "partition_index": partition,
                            "evidence": evidence,
                        }
                        iteration["passes"][pass_name] = pass_evidence
                        iteration["tightened_upper_bound"] = upper
                        iterations.append(iteration)
                        restart = True
                        break
                    complete_unsat = bool(
                        outcome == "unsat"
                        and evidence.get("decision_complete") is True
                        and evidence.get("threshold_infeasible") is True
                        and evidence.get("success") is False
                        and evidence.get("operator") is None
                    )
                    if not complete_unsat:
                        iteration["passes"][pass_name] = pass_evidence
                        iterations.append(iteration)
                        result = _result_base(
                            job,
                            status=INCOMPLETE,
                            started_at=started_at,
                            now=clock(),
                            lower_bound=lower_bound,
                            upper_bound=upper,
                            upper_witness=upper_witness,
                            iterations=iterations,
                            reason=f"{pass_name} {sector}/{partition} returned {outcome or 'unknown'}",
                        )
                        _write_provisional_result(paths, result)
                        return result
                if restart:
                    break
            if restart:
                break
            iteration["passes"][pass_name] = pass_evidence
            if pass_name == "build":
                lower_bound = upper
                provisional = _result_base(
                    job,
                    status=LOWER_BOUND_PROVEN,
                    started_at=started_at,
                    now=clock(),
                    lower_bound=lower_bound,
                    upper_bound=upper,
                    upper_witness=upper_witness,
                    iterations=iterations + [iteration],
                    reason="independent verification pass remains",
                )
                _write_provisional_result(paths, provisional)
                _update_claim(
                    paths,
                    job_id=job["job_id"],
                    worker_id=worker_id,
                    attempt=int(job["attempts"]),
                    claim_token=str(job["claim_token"]),
                    state=LOWER_BOUND_PROVEN,
                )
        if restart:
            continue
        iterations.append(iteration)
        result = _result_base(
            job,
            status=EXACT_DISTANCE_PROVEN,
            started_at=started_at,
            now=clock(),
            lower_bound=upper,
            upper_bound=upper,
            upper_witness=upper_witness,
            iterations=iterations,
        )
        _write_provisional_result(paths, result)
        return result


def complete_job(
    paths: QueuePaths,
    *,
    job_id: str,
    worker_id: str,
    result: Mapping[str, Any],
    now: float | None = None,
) -> dict[str, Any]:
    """Publish a result only after validating the live claim under the lock."""

    _assert_source_unchanged()
    result = _validate_result(result)
    if result.get("exactifier_source_sha256") != _source_sha256():
        raise ValueError("result exactifier source differs from this worker")
    timestamp = time.time() if now is None else float(now)
    with _QueueLock(paths):
        queue = _load_queue(paths)
        live = next(
            (job for job in queue["jobs"] if job["job_id"] == job_id),
            None,
        )
        claim_matches = bool(
            live is not None
            and live.get("claimed_by") == worker_id
            and live.get("state") in OWNED_STATES
            and result.get("job_id") == job_id
            and result.get("input_sha256") == live.get("input_sha256")
            and result.get("attempt") == live.get("attempts")
            and result.get("claim_worker_id") == worker_id
            and result.get("claim_token") == live.get("claim_token")
            and result.get("job_sha256")
            == live.get("proof_job_sha256", live.get("job_sha256"))
            and result.get("policy_sha256")
            == live.get("proof_policy_sha256")
            and result.get("proof_policy") == live.get("proof_policy")
        )
        if not claim_matches:
            stale_path = _result_artifact_path(
                paths,
                result,
                disposition="stale",
            )
            _write_immutable_json(stale_path, result)
            raise ValueError(
                "exactification result lost its live claim; preserved as immutable stale evidence"
            )

        assert live is not None
        result_path = _result_artifact_path(
            paths,
            result,
            disposition="accepted",
        )
        _write_immutable_json(result_path, result)
        config = QueueConfig.from_json(queue["config"])
        terminal_state = str(result["status"])
        jobs: list[dict[str, Any]] = []
        for raw in queue["jobs"]:
            job = dict(raw)
            if job["job_id"] == job_id:
                job.update({
                    "state": terminal_state if job["active"] else RETIRED,
                    "claimed_by": None,
                    "claimed_at": None,
                    "heartbeat_at": None,
                    "claim_token": None,
                    "updated_at": timestamp,
                    "result_path": str(result_path.resolve()),
                    "result_sha256": result["result_sha256"],
                    "last_error": (
                        result.get("reason")
                        if terminal_state in {INCOMPLETE, ERROR}
                        else None
                    ),
                    "next_attempt_at": None,
                })
                if terminal_state in {INCOMPLETE, ERROR} and job["active"]:
                    exponent = max(0, int(job["attempts"]) - 1)
                    delay = min(
                        float(config.retry_backoff_max_s),
                        float(config.retry_backoff_s) * (2 ** exponent),
                    )
                    job["next_attempt_at"] = timestamp + delay
                if not job["active"]:
                    job["terminal_result_state"] = terminal_state
                    job["retirement_pending"] = False
                job = _seal_job(job)
            jobs.append(job)
        queue["jobs"] = jobs
        queue.update({
            "revision": int(queue["revision"]) + 1,
            "updated_at": timestamp,
        })
        return _write_queue(paths, queue)

def queue_status(paths: QueuePaths) -> dict[str, Any]:
    queue = _load_queue(paths)
    counts = {state: 0 for state in sorted(JOB_STATES)}
    active = 0
    for job in queue["jobs"]:
        counts[job["state"]] += 1
        active += int(job["active"])
    return {
        "queue_sha256": queue["queue_sha256"],
        "revision": queue["revision"],
        "updated_at": queue["updated_at"],
        "active_jobs": active,
        "counts": counts,
        "jobs": [
            {
                key: job.get(key)
                for key in (
                    "job_id",
                    "rank",
                    "active",
                    "state",
                    "attempts",
                    "claimed_by",
                    "heartbeat_at",
                    "next_attempt_at",
                    "result_path",
                    "last_error",
                )
            }
            for job in queue["jobs"]
        ],
    }


def worker_loop(
    *,
    paths: QueuePaths,
    config: QueueConfig = QueueConfig(),
    worker_id: str | None = None,
    once: bool = False,
    refresh_callback: Callable[[], Any] | None = None,
    stop_event: Any | None = None,
    sleep_fn: Callable[[float], Any] = time.sleep,
) -> dict[str, Any]:
    """Claim and run jobs; capacity gating and process leases stay in the CLI."""

    config = config.validate()
    worker_id = worker_id or f"{os.getpid()}-{uuid.uuid4().hex}"
    processed = 0
    while stop_event is None or not stop_event.is_set():
        job = claim_next_job(paths, worker_id=worker_id, config=config)
        if job is None and refresh_callback is not None:
            refresh_callback()
            job = claim_next_job(paths, worker_id=worker_id, config=config)
        if job is None:
            if once:
                break
            sleep_fn(float(config.poll_interval_s))
            continue
        result = exactify_job(
            job,
            paths=paths,
            config=config,
            cancel_event=stop_event,
        )
        complete_job(
            paths,
            job_id=job["job_id"],
            worker_id=worker_id,
            result=result,
        )
        processed += 1
        if once:
            break
    return {"worker_id": worker_id, "processed": processed, "status": queue_status(paths)}


__all__ = [
    "ERROR",
    "EXACT_DISTANCE_PROVEN",
    "INCOMPLETE",
    "LOWER_BOUND_PROVEN",
    "PENDING",
    "QueueConfig",
    "QueuePaths",
    "claim_next_job",
    "complete_job",
    "exactify_job",
    "queue_paths",
    "queue_status",
    "recover_stale_jobs",
    "refresh_queue",
    "validate_queue",
    "worker_loop",
]
