"""Durable, non-publication SAT sidecar for strict Stage-2 near misses.

The queue owns no pipeline state.  Its proof atoms are concrete
``(candidate, lane, sector, first-nonzero partition, timeout slice)`` SAT
decisions.  UNKNOWN, timeout, cancellation and backend failure are always
incomplete.  A lane raises a lower bound only after every X and Z partition
is independently validated as UNSAT; strict success additionally requires
two complete lanes with different solver/encoding pairs.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import math
import os
import re
import stat
import threading
import time
import uuid
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

import numpy as np


SCHEMA_VERSION = 1
SIDECAR_NAME = "stage2-strict-deep-v1"
QUEUE_GATE = "qldpc-stage2-strict-deep-queue"
RESULT_GATE = "qldpc-stage2-strict-deep-unit-result"
UNIT_GATE = "qldpc-stage2-strict-deep-sat-unit"

PENDING = "PENDING"
RUNNING = "RUNNING"
UNSAT = "UNSAT"
SAT = "SAT"
INCOMPLETE = "INCOMPLETE"
LOWER_BOUND_PROVEN = "LOWER_BOUND_PROVEN"
STRICT_THRESHOLD_PROVEN = "STRICT_THRESHOLD_PROVEN"
WITNESS_REJECTED = "WITNESS_REJECTED"
PRIMARY_THRESHOLD_PROVEN = "PRIMARY_THRESHOLD_PROVEN"

_UNIT_STATES = frozenset({PENDING, RUNNING, UNSAT, SAT, INCOMPLETE})
_CANDIDATE_STATES = frozenset({
    PENDING,
    RUNNING,
    INCOMPLETE,
    PRIMARY_THRESHOLD_PROVEN,
    STRICT_THRESHOLD_PROVEN,
    WITNESS_REJECTED,
})

_SOLVERS = frozenset({
    "cadical153", "cadical195", "cadical300", "kissat404",
    "glucose4", "glucose42", "minisat22", "minicard",
})
_ENCODINGS = frozenset({
    "seqcounter", "totalizer", "kmtotalizer", "native-minicard",
})

try:
    _SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
except OSError:
    _SOURCE_SHA256 = None


def _assert_source_unchanged() -> str:
    if _SOURCE_SHA256 is None:
        raise RuntimeError("strict deep source could not be frozen at import")
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != _SOURCE_SHA256:
        raise RuntimeError("strict deep source changed while the worker was running")
    return _SOURCE_SHA256


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str) and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _read_json(path: Path, *, label: str) -> tuple[dict[str, Any], str]:
    before = path.lstat()
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        raise ValueError(f"{label} must be a regular non-symlink file")
    payload = path.read_bytes()
    after = path.lstat()
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
    ):
        raise ValueError(f"{label} changed while reading")
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"{label} is malformed JSON") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain an object")
    return value, hashlib.sha256(payload).hexdigest()


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    try:
        with temporary.open("wb") as stream:
            stream.write(_canonical_bytes(dict(value)) + b"\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        descriptor = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)


def _write_immutable_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = _canonical_bytes(dict(value)) + b"\n"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError:
        if path.read_bytes() != payload:
            raise ValueError("immutable deep artifact collision")
        return
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    directory = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


@dataclass(frozen=True)
class LaneSpec:
    name: str
    solver: str
    cardinality_encoding: str

    @classmethod
    def from_mapping(cls, value: Mapping[str, Any]) -> "LaneSpec":
        allowed = {"name", "solver", "cardinality_encoding"}
        if set(value) - allowed:
            raise ValueError("unknown strict deep lane settings")
        return cls(**dict(value)).validate()

    def validate(self) -> "LaneSpec":
        if (
            not isinstance(self.name, str)
            or re.fullmatch(r"[a-z0-9][a-z0-9-]{0,63}", self.name) is None
        ):
            raise ValueError("lane name must be a safe nonempty identifier")
        if self.solver not in _SOLVERS or self.solver == "auto":
            raise ValueError("lane requires a concrete supported solver")
        if self.cardinality_encoding not in _ENCODINGS:
            raise ValueError("unsupported cardinality encoding")
        if (self.cardinality_encoding == "native-minicard") != (
            self.solver == "minicard"
        ):
            raise ValueError("native-minicard and solver=minicard must be paired")
        return self


@dataclass(frozen=True)
class DeepConfig:
    lanes: tuple[LaneSpec, ...] = (
        LaneSpec("cadical-seq", "cadical195", "seqcounter"),
        LaneSpec("kissat-total", "kissat404", "totalizer"),
        LaneSpec("glucose-km", "glucose42", "kmtotalizer"),
        LaneSpec("minicard-native", "minicard", "native-minicard"),
    )
    time_slices_s: tuple[float, ...] = (1800.0, 7200.0, 21600.0)
    required_proof_lanes: int = 2
    max_workers: int = 4
    seed: int = 0
    poll_interval_s: float = 30.0
    stale_after_s: float = 28800.0
    termination_grace_s: float = 180.0

    def validate(self) -> "DeepConfig":
        if len(self.lanes) < 2 or any(not isinstance(item, LaneSpec) for item in self.lanes):
            raise ValueError("at least two typed deep solver lanes are required")
        for lane in self.lanes:
            lane.validate()
        signatures = {(lane.solver, lane.cardinality_encoding) for lane in self.lanes}
        if len(signatures) != len(self.lanes):
            raise ValueError("deep solver lanes must have distinct configurations")
        if not 2 <= self.required_proof_lanes <= len(self.lanes):
            raise ValueError("required_proof_lanes must be between 2 and lane count")
        if len({lane.solver for lane in self.lanes}) != len(self.lanes):
            raise ValueError("every deep proof lane must use a distinct concrete solver")
        if isinstance(self.max_workers, bool) or not isinstance(self.max_workers, int):
            raise ValueError("max_workers must be an integer")
        if not 1 <= self.max_workers <= 4:
            raise ValueError("deep sidecar max_workers must be between 1 and 4")
        if isinstance(self.seed, bool) or not isinstance(self.seed, int):
            raise ValueError("seed must be an integer")
        if not self.time_slices_s:
            raise ValueError("time_slices_s must be nonempty")
        previous = 0.0
        for value in self.time_slices_s:
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError("time slices must be numeric")
            number = float(value)
            if not math.isfinite(number) or number <= previous:
                raise ValueError("time slices must be positive, finite, and increasing")
            previous = number
        for name, value in (
            ("poll_interval_s", self.poll_interval_s),
            ("stale_after_s", self.stale_after_s),
            ("termination_grace_s", self.termination_grace_s),
        ):
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError(f"{name} must be numeric")
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ValueError(f"{name} must be positive and finite")
        return self

    @classmethod
    def from_json(cls, source: Path | str | Mapping[str, Any]) -> "DeepConfig":
        raw: Any
        if isinstance(source, Mapping):
            raw = dict(source)
        else:
            raw, _ = _read_json(Path(source), label="strict deep config")
        if "queue" in raw:
            raw = raw["queue"]
        if not isinstance(raw, Mapping):
            raise ValueError("strict deep queue config must be an object")
        allowed = set(cls.__dataclass_fields__)
        if set(raw) - allowed:
            raise ValueError("unknown strict deep queue settings")
        values = dict(raw)
        if "lanes" in values:
            if not isinstance(values["lanes"], list):
                raise ValueError("lanes must be a list")
            values["lanes"] = tuple(LaneSpec.from_mapping(item) for item in values["lanes"])
        if "time_slices_s" in values:
            values["time_slices_s"] = tuple(values["time_slices_s"])
        return cls(**values).validate()

    def as_dict(self) -> dict[str, Any]:
        self.validate()
        value = asdict(self)
        value["lanes"] = [asdict(lane) for lane in self.lanes]
        value["time_slices_s"] = list(self.time_slices_s)
        return value


@dataclass(frozen=True)
class DeepPaths:
    run_root: Path
    root: Path
    queue: Path
    lock: Path
    journal: Path
    evidence: Path
    checkpoints: Path


def deep_paths(run_root: Path | str, *, state_dir: Path | str | None = None) -> DeepPaths:
    run = Path(run_root).expanduser().resolve(strict=True)
    root = (run / "sidecars" / SIDECAR_NAME) if state_dir is None else Path(state_dir)
    root = root.expanduser().resolve(strict=False)
    try:
        root.relative_to(run)
    except ValueError as exc:
        raise ValueError("strict deep state directory escapes pipeline run") from exc
    return DeepPaths(
        run_root=run,
        root=root, queue=root / "queue.json", lock=root / "queue.lock",
        journal=root / "journal", evidence=root / "evidence",
        checkpoints=root / "checkpoints",
    )


class _QueueLock:
    def __init__(self, paths: DeepPaths) -> None:
        paths.root.mkdir(parents=True, exist_ok=True)
        self._stream = paths.lock.open("a+b")

    def __enter__(self) -> "_QueueLock":
        fcntl.flock(self._stream.fileno(), fcntl.LOCK_EX)
        return self

    def __exit__(self, *_: Any) -> None:
        fcntl.flock(self._stream.fileno(), fcntl.LOCK_UN)
        self._stream.close()


def _seal_queue(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result.pop("queue_sha256", None)
    result["queue_sha256"] = canonical_sha256(result)
    return result


def validate_queue(value_or_path: Mapping[str, Any] | Path | str) -> dict[str, Any]:
    queue_path: Path | None = None
    if isinstance(value_or_path, Mapping):
        value = dict(value_or_path)
    else:
        queue_path = Path(value_or_path).expanduser().resolve(strict=True)
        value = _read_json(queue_path, label="strict deep queue")[0]
    digest = value.get("queue_sha256")
    unsigned = dict(value)
    unsigned.pop("queue_sha256", None)
    if (
        value.get("schema_version") != SCHEMA_VERSION
        or value.get("gate") != QUEUE_GATE
        or not _is_sha256(digest)
        or digest != canonical_sha256(unsigned)
        or not isinstance(value.get("candidates"), list)
        or not isinstance(value.get("policy"), Mapping)
        or value.get("policy_sha256") != canonical_sha256(value["policy"])
    ):
        raise ValueError("strict deep queue seal is invalid")
    config = DeepConfig.from_json(value["policy"])
    revision = value.get("revision")
    if (
        isinstance(revision, bool)
        or not isinstance(revision, int)
        or revision < 0
        or value.get("status") not in {
            RUNNING, INCOMPLETE, STRICT_THRESHOLD_PROVEN, WITNESS_REJECTED,
        }
    ):
        raise ValueError("strict deep queue lifecycle is invalid")
    _validate_candidate_records(value, config)
    if queue_path is not None:
        _validate_evidence_files(value, queue_path=queue_path)
    return value


def _validate_evidence_files(
    queue: Mapping[str, Any],
    *,
    queue_path: Path,
) -> None:
    state_root = (
        queue_path.parent.parent
        if queue_path.parent.name == "journal"
        else queue_path.parent
    )
    accepted_root = (state_root / "evidence" / "accepted").resolve(strict=False)
    for candidate in queue["candidates"]:
        for lane in candidate["lanes"]:
            for unit in lane["units"]:
                reference = unit.get("evidence")
                if reference is None:
                    continue
                evidence_path = Path(str(reference["path"])).expanduser().resolve(
                    strict=True,
                )
                try:
                    evidence_path.relative_to(accepted_root)
                except ValueError as exc:
                    raise ValueError("strict deep evidence escapes accepted root") from exc
                metadata = evidence_path.lstat()
                if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
                    raise ValueError("strict deep evidence is not a regular file")
                result = _validate_result(
                    _read_json(evidence_path, label="strict deep evidence")[0],
                )
                expected = {
                    "canonical_digest": candidate["canonical_digest"],
                    "lane": {
                        "name": lane["name"],
                        "solver": lane["solver"],
                        "cardinality_encoding": lane["cardinality_encoding"],
                    },
                    "sector": unit["sector"],
                    "partition_index": unit["partition_index"],
                    "status": unit["status"],
                    "result_sha256": reference["result_sha256"],
                    "cutoff": candidate["cutoff"],
                    "objective": reference.get("objective"),
                }
                if unit["status"] in {SAT, UNSAT}:
                    expected["checkpoint_identity"] = _checkpoint_identity(
                        candidate, lane, unit, queue_source=queue["source"],
                    )
                if any(result.get(key) != expected_value for key, expected_value in expected.items()):
                    raise ValueError("strict deep evidence does not match its queue unit")
                if evidence_path.name.rsplit("-", 1)[-1] != (
                    f"{result['result_sha256']}.json"
                ):
                    raise ValueError("strict deep evidence filename is not content-bound")


def _write_queue(paths: DeepPaths, value: Mapping[str, Any]) -> dict[str, Any]:
    sealed = _seal_queue(value)
    validate_queue(sealed)
    _validate_evidence_files(sealed, queue_path=paths.queue)
    snapshot = paths.journal / (
        f"revision-{int(sealed['revision']):08d}-{sealed['queue_sha256']}.json"
    )
    _write_immutable_json(snapshot, sealed)
    _atomic_write_json(paths.queue, sealed)
    validate_queue(paths.queue)
    return sealed


def queue_status(paths: DeepPaths) -> dict[str, Any]:
    if not paths.queue.exists():
        return {"status": "NOT_STARTED", "root": str(paths.root)}
    queue = validate_queue(paths.queue)
    counts: dict[str, int] = {}
    for candidate in queue["candidates"]:
        status = str(candidate.get("status"))
        counts[status] = counts.get(status, 0) + 1
    return {
        "status": "READY", "root": str(paths.root),
        "revision": queue["revision"], "candidate_status_counts": counts,
        "candidates": [
            {
                "canonical_digest": item.get("canonical_digest"),
                "status": item.get("status"), "bounds": item.get("bounds"),
                "proven_lanes": item.get("proven_lanes", []),
            }
            for item in queue["candidates"]
        ],
        "publication_certificate": False,
        "pipeline_promotion": False,
    }


def _confined_regular(path: Path | str, *, root: Path, label: str) -> Path:
    value = Path(path).expanduser().resolve(strict=True)
    try:
        value.relative_to(root)
    except ValueError as exc:
        raise ValueError(f"{label} escapes the pipeline run") from exc
    metadata = value.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise ValueError(f"{label} must be a regular non-symlink file")
    return value


def _stable_jsonl(path: Path, *, label: str) -> tuple[list[dict[str, Any]], str]:
    before = path.lstat()
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        raise ValueError(f"{label} must be a regular non-symlink file")
    payload = path.read_bytes()
    after = path.lstat()
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
    ):
        raise ValueError(f"{label} changed while reading")
    rows: list[dict[str, Any]] = []
    for line_number, raw in enumerate(payload.splitlines(), start=1):
        if not raw.strip():
            continue
        try:
            value = json.loads(raw)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError(f"{label}:{line_number} is malformed") from exc
        if not isinstance(value, dict):
            raise ValueError(f"{label}:{line_number} is not an object")
        rows.append(value)
    return rows, hashlib.sha256(payload).hexdigest()


def _array_identity(label: str, value: Any) -> dict[str, Any]:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    header = f"{label}:{array.shape}:{array.dtype.str}:".encode()
    return {
        "label": label,
        "shape": list(array.shape),
        "sha256": hashlib.sha256(header + array.tobytes()).hexdigest(),
    }


def _candidate_digest(row: Mapping[str, Any]) -> str:
    value = row.get("canonical_digest")
    if not _is_sha256(value):
        identity = row.get("triage_identity")
        raw = identity.get("canonical_digest") if isinstance(identity, Mapping) else None
        if isinstance(raw, str) and ":" in raw:
            raw = raw.rsplit(":", 1)[-1]
        value = raw
    if not _is_sha256(value):
        raise ValueError("strict deep source row lacks a canonical digest")
    return str(value)


def _unit_id(lane_name: str, sector: str, partition: int) -> str:
    return f"{lane_name}:{sector}:{partition}"


def _new_lane(lane: LaneSpec, k: int) -> dict[str, Any]:
    return {
        "name": lane.name,
        "solver": lane.solver,
        "cardinality_encoding": lane.cardinality_encoding,
        "status": PENDING,
        "slice_index": 0,
        "units": [
            {
                "unit_id": _unit_id(lane.name, sector, partition),
                "sector": sector,
                "partition_index": partition,
                "status": PENDING,
                "attempt": 0,
                "slice_index": 0,
                "retry_same_slice": False,
                "claim_token": None,
                "evidence": None,
            }
            for sector in ("X", "Z")
            for partition in range(k)
        ],
    }


def _lane_is_proven(lane: Mapping[str, Any], k: int) -> bool:
    units = lane.get("units")
    return bool(
        isinstance(units, list)
        and len(units) == 2 * k
        and all(
            isinstance(unit, Mapping) and unit.get("status") == UNSAT
            for unit in units
        )
    )


def _derived_candidate_status(
    candidate: Mapping[str, Any],
    *,
    required_lanes: int,
) -> tuple[str, list[str]]:
    lanes = candidate.get("lanes")
    if not isinstance(lanes, list):
        raise ValueError("strict deep candidate lanes are malformed")
    if any(
        isinstance(unit, Mapping) and unit.get("status") == SAT
        for lane in lanes if isinstance(lane, Mapping)
        for unit in lane.get("units", []) if isinstance(lane.get("units"), list)
    ):
        return WITNESS_REJECTED, []
    k = int(candidate["k"])
    proven = [
        str(lane["name"]) for lane in lanes
        if isinstance(lane, Mapping) and _lane_is_proven(lane, k)
    ]
    if len(proven) >= required_lanes:
        return STRICT_THRESHOLD_PROVEN, proven
    if proven:
        return PRIMARY_THRESHOLD_PROVEN, proven
    if any(
        isinstance(unit, Mapping) and unit.get("status") == RUNNING
        for lane in lanes if isinstance(lane, Mapping)
        for unit in lane.get("units", []) if isinstance(lane.get("units"), list)
    ):
        return RUNNING, proven
    attempted = any(
        isinstance(unit, Mapping) and unit.get("status") != PENDING
        for lane in lanes if isinstance(lane, Mapping)
        for unit in lane.get("units", []) if isinstance(lane.get("units"), list)
    )
    return (INCOMPLETE if attempted else PENDING), proven


def _validate_candidate_record(
    candidate: Mapping[str, Any],
    *,
    config: DeepConfig,
) -> None:
    digest = candidate.get("canonical_digest")
    n = candidate.get("n")
    k = candidate.get("k")
    required = candidate.get("required_distance")
    cutoff = candidate.get("cutoff")
    if (
        not _is_sha256(digest)
        or isinstance(n, bool) or not isinstance(n, int) or n <= 0
        or isinstance(k, bool) or not isinstance(k, int) or k <= 0
        or isinstance(required, bool) or not isinstance(required, int) or required <= 0
        or cutoff != required - 1
        or k * cutoff * cutoff <= 0
        or not (k * cutoff * cutoff <= 12 * n < k * required * required)
    ):
        raise ValueError("strict deep candidate target is invalid")
    bounds = candidate.get("bounds")
    if (
        not isinstance(bounds, Mapping)
        or isinstance(bounds.get("lower"), bool)
        or not isinstance(bounds.get("lower"), int)
        or isinstance(bounds.get("upper"), bool)
        or not isinstance(bounds.get("upper"), int)
        or not 1 <= bounds["lower"] <= bounds["upper"] <= n
    ):
        raise ValueError("strict deep candidate bounds are invalid")
    matrices = candidate.get("matrices")
    if (
        not isinstance(matrices, Mapping)
        or set(matrices) != {"hx", "hz", "lx", "lz", "bundle_sha256"}
        or matrices.get("bundle_sha256") != canonical_sha256({
            key: matrices[key] for key in ("hx", "hz", "lx", "lz")
        })
    ):
        raise ValueError("strict deep candidate matrix identity is invalid")
    lanes = candidate.get("lanes")
    if not isinstance(lanes, list) or len(lanes) != len(config.lanes):
        raise ValueError("strict deep candidate lane count is invalid")
    expected_units = {(sector, partition) for sector in ("X", "Z") for partition in range(k)}
    for stored, expected in zip(lanes, config.lanes, strict=True):
        if (
            not isinstance(stored, Mapping)
            or stored.get("name") != expected.name
            or stored.get("solver") != expected.solver
            or stored.get("cardinality_encoding") != expected.cardinality_encoding
            or not isinstance(stored.get("units"), list)
        ):
            raise ValueError("strict deep lane identity is invalid")
        observed: set[tuple[str, int]] = set()
        for unit in stored["units"]:
            if not isinstance(unit, Mapping):
                raise ValueError("strict deep unit is malformed")
            sector = unit.get("sector")
            partition = unit.get("partition_index")
            if (
                sector not in {"X", "Z"}
                or isinstance(partition, bool)
                or not isinstance(partition, int)
                or unit.get("unit_id") != _unit_id(expected.name, sector, partition)
                or unit.get("status") not in _UNIT_STATES
                or isinstance(unit.get("attempt"), bool)
                or not isinstance(unit.get("attempt"), int)
                or unit["attempt"] < 0
                or isinstance(unit.get("slice_index"), bool)
                or not isinstance(unit.get("slice_index"), int)
                or not 0 <= unit["slice_index"] < len(config.time_slices_s)
                or not isinstance(unit.get("retry_same_slice"), bool)
                or (unit["status"] != INCOMPLETE and unit["retry_same_slice"])
            ):
                raise ValueError("strict deep unit identity/state is invalid")
            observed.add((sector, partition))
            evidence = unit.get("evidence")
            if unit["status"] in {SAT, UNSAT}:
                if (
                    not isinstance(evidence, Mapping)
                    or not _is_sha256(evidence.get("result_sha256"))
                    or not isinstance(evidence.get("path"), str)
                    or evidence.get("outcome")
                    != ("sat" if unit["status"] == SAT else "unsat")
                ):
                    raise ValueError("terminal strict deep unit lacks evidence")
                objective = evidence.get("objective")
                if unit["status"] == SAT and (
                    isinstance(objective, bool)
                    or not isinstance(objective, int)
                    or not 1 <= objective <= cutoff
                ):
                    raise ValueError("terminal SAT unit lacks a bounded objective")
                if unit["status"] == UNSAT and objective is not None:
                    raise ValueError("terminal UNSAT unit cannot carry an objective")
            elif evidence is not None and not isinstance(evidence, Mapping):
                raise ValueError("strict deep unit evidence reference is malformed")
        if observed != expected_units or len(stored["units"]) != len(expected_units):
            raise ValueError("strict deep lane does not cover X/Z first-nonzero units")
        unit_statuses = [unit["status"] for unit in stored["units"]]
        expected_lane_status = (
            SAT if SAT in unit_statuses
            else UNSAT if all(value == UNSAT for value in unit_statuses)
            else RUNNING if RUNNING in unit_statuses
            else INCOMPLETE if any(value != PENDING for value in unit_statuses)
            else PENDING
        )
        if stored.get("status") != expected_lane_status:
            raise ValueError("strict deep lane aggregate status is inconsistent")
    status, proven = _derived_candidate_status(
        candidate, required_lanes=config.required_proof_lanes,
    )
    if candidate.get("status") != status or candidate.get("proven_lanes") != proven:
        raise ValueError("strict deep candidate aggregate status is inconsistent")
    if (
        status in {PRIMARY_THRESHOLD_PROVEN, STRICT_THRESHOLD_PROVEN}
        and bounds["lower"] != required
    ):
        raise ValueError("strict deep proven candidate lacks the required lower bound")
    if status == WITNESS_REJECTED and bounds["upper"] > cutoff:
        raise ValueError("strict deep rejected candidate lacks a threshold witness bound")
    if candidate.get("requires_independent_replay") is not (
        status == PRIMARY_THRESHOLD_PROVEN
    ):
        raise ValueError("strict deep independent-replay flag is inconsistent")


def _validate_candidate_records(value: Mapping[str, Any], config: DeepConfig) -> None:
    candidates = value.get("candidates")
    if not isinstance(candidates, list) or len(candidates) != 2:
        raise ValueError("strict deep v1 requires exactly two candidates")
    digests: set[str] = set()
    for candidate in candidates:
        if not isinstance(candidate, Mapping):
            raise ValueError("strict deep candidate is malformed")
        _validate_candidate_record(candidate, config=config)
        digest = str(candidate["canonical_digest"])
        if digest in digests:
            raise ValueError("strict deep queue contains duplicate candidates")
        digests.add(digest)
    source = value.get("source")
    if (
        not isinstance(source, Mapping)
        or not isinstance(source.get("ranked_input"), str)
        or not _is_sha256(source.get("ranked_input_sha256"))
        or not isinstance(source.get("summary_input"), str)
        or not _is_sha256(source.get("summary_input_sha256"))
        or source.get("expected_digests")
        != [candidate["canonical_digest"] for candidate in candidates]
    ):
        raise ValueError("strict deep queue source provenance is invalid")
    statuses = [candidate["status"] for candidate in candidates]
    if STRICT_THRESHOLD_PROVEN in statuses:
        expected_queue_statuses = {STRICT_THRESHOLD_PROVEN}
    elif all(status == WITNESS_REJECTED for status in statuses):
        expected_queue_statuses = {WITNESS_REJECTED}
    else:
        expected_queue_statuses = {RUNNING, INCOMPLETE}
    if value.get("status") not in expected_queue_statuses:
        raise ValueError("strict deep queue aggregate status is inconsistent")
    if value.get("publication_certificate") is not False or value.get(
        "pipeline_promotion"
    ) is not False:
        raise ValueError("strict deep v1 cannot claim publication or pipeline authority")


def initialize_queue(
    paths: DeepPaths,
    *,
    ranked_input: Path | str,
    summary_input: Path | str,
    expected_digests: Sequence[str],
    config: DeepConfig = DeepConfig(),
    now: float | None = None,
) -> dict[str, Any]:
    """Create the two-candidate queue from one sealed strict-discovery batch."""

    config = config.validate()
    if len(expected_digests) != 2 or len(set(expected_digests)) != 2 or any(
        not _is_sha256(value) for value in expected_digests
    ):
        raise ValueError("strict deep initialization requires two distinct digests")
    ranked_path = _confined_regular(
        ranked_input, root=paths.run_root, label="strict ranked input",
    )
    summary_path = _confined_regular(
        summary_input, root=paths.run_root, label="strict summary input",
    )
    rows, ranked_sha = _stable_jsonl(ranked_path, label="strict ranked input")
    summary, summary_sha = _read_json(summary_path, label="strict summary input")
    if (
        summary.get("gate") != "qldpc-proof-oriented-candidate-pool"
        or summary.get("target_mode") != "scalar-fom-strict-v1"
        or summary.get("certified_wins") != 0
        or not isinstance(summary.get("results"), list)
    ):
        raise ValueError("strict summary is not a no-win strict candidate batch")
    summary_rows = {
        item.get("canonical_digest"): item
        for item in summary["results"]
        if isinstance(item, Mapping) and item.get("status") == "UNRESOLVED"
    }
    if set(summary_rows) != set(expected_digests):
        raise ValueError("strict summary unresolved set is not exactly the requested pair")
    indexed: dict[str, dict[str, Any]] = {}
    for row in rows:
        digest = _candidate_digest(row)
        if digest in expected_digests:
            if digest in indexed:
                raise ValueError("strict ranked input duplicates a requested candidate")
            indexed[digest] = row
    if set(indexed) != set(expected_digests):
        raise ValueError("strict ranked input does not contain the requested pair")

    from evaluation.distance_milp import get_code_matrices
    from scripts.audit_direction_pool import candidate_from_stage2
    from scripts.screen_frontier_candidate import build_candidate_code

    candidates: list[dict[str, Any]] = []
    for digest in expected_digests:
        row = indexed[digest]
        candidate = candidate_from_stage2(
            row, target_mode="scalar-fom-strict-v1",
        )
        if candidate["canonical_digest"].rsplit(":", 1)[-1] != digest:
            raise ValueError("strict candidate identity changed during reconstruction")
        code = build_candidate_code(candidate)
        hx, hz, lx, lz = (
            np.asarray(value, dtype=np.uint8) & 1
            for value in get_code_matrices(code)
        )
        n = int(candidate["n"])
        k = int(candidate["k"])
        required = int(candidate["required_distance"])
        if (
            int(code.num_qudits) != n
            or int(code.dimension) != k
            or lx.shape[0] != k
            or lz.shape[0] != k
        ):
            raise ValueError("strict candidate reconstruction changed n/k")
        matrix_rows = {
            "hx": _array_identity("hx", hx),
            "hz": _array_identity("hz", hz),
            "lx": _array_identity("lx", lx),
            "lz": _array_identity("lz", lz),
        }
        matrices = {
            **matrix_rows,
            "bundle_sha256": canonical_sha256(matrix_rows),
        }
        lower = row.get("distance_lower_bound")
        upper = row.get("distance_upper_bound")
        if (
            row.get("distance_lower_bound_proven") is not True
            or isinstance(lower, bool) or not isinstance(lower, int)
            or isinstance(upper, bool) or not isinstance(upper, int)
            or not 1 <= lower <= upper <= n
        ):
            raise ValueError("strict candidate lacks finite authenticated LB/UB")
        audit_path = _confined_regular(
            str(summary_rows[digest].get("audit_path")),
            root=paths.run_root,
            label=f"strict audit artifact {digest}",
        )
        audit, audit_sha = _read_json(audit_path, label="strict audit artifact")
        if audit.get("status") != "UNRESOLVED":
            raise ValueError("strict audit artifact is not unresolved")
        for sector_record in audit.get("sectors", []):
            if (
                not isinstance(sector_record, Mapping)
                or sector_record.get("status_name") != "UNKNOWN"
                or sector_record.get("threshold_infeasible") is True
            ):
                raise ValueError("strict audit history contains unexpected proof evidence")
        record: dict[str, Any] = {
            "canonical_digest": digest,
            "candidate_input_sha256": canonical_sha256(candidate),
            "candidate": candidate,
            "source_row_sha256": canonical_sha256(row),
            "n": n,
            "k": k,
            "required_distance": required,
            "cutoff": required - 1,
            "target_binding_sha256": candidate["target"]["binding_sha256"],
            "matrices": matrices,
            "bounds": {
                "lower": lower,
                "upper": upper,
                "lower_source": row.get("distance_lower_bound_status"),
                "upper_source": row.get("distance_upper_bound_source"),
            },
            "historical_unknown": {
                "artifact_path": str(audit_path),
                "artifact_sha256": audit_sha,
                "completed_proof_units": 0,
            },
            "lanes": [_new_lane(lane, k) for lane in config.lanes],
            "status": PENDING,
            "proven_lanes": [],
            "requires_independent_replay": False,
            "updated_at": time.time() if now is None else float(now),
        }
        candidates.append(record)
    timestamp = time.time() if now is None else float(now)
    value = {
        "schema_version": SCHEMA_VERSION,
        "gate": QUEUE_GATE,
        "status": RUNNING,
        "revision": 0,
        "created_at": timestamp,
        "updated_at": timestamp,
        "policy": config.as_dict(),
        "policy_sha256": canonical_sha256(config.as_dict()),
        "source": {
            "ranked_input": str(ranked_path),
            "ranked_input_sha256": ranked_sha,
            "summary_input": str(summary_path),
            "summary_input_sha256": summary_sha,
            "expected_digests": list(expected_digests),
        },
        "candidates": candidates,
        "publication_certificate": False,
        "pipeline_promotion": False,
    }
    _validate_candidate_records(value, config)
    with _QueueLock(paths):
        if paths.queue.exists():
            existing = validate_queue(paths.queue)
            if existing.get("source") != value["source"] or existing.get(
                "policy_sha256"
            ) != value["policy_sha256"]:
                raise ValueError("existing strict deep queue has different inputs")
            return existing
        return _write_queue(paths, value)


def _load_candidate_matrices(candidate_record: Mapping[str, Any]) -> tuple[
    np.ndarray, np.ndarray, np.ndarray, np.ndarray,
]:
    from evaluation.distance_milp import get_code_matrices
    from scripts.screen_frontier_candidate import build_candidate_code

    candidate = candidate_record.get("candidate")
    if (
        not isinstance(candidate, Mapping)
        or canonical_sha256(candidate) != candidate_record.get("candidate_input_sha256")
    ):
        raise ValueError("strict deep candidate input seal is invalid")
    code = build_candidate_code(dict(candidate))
    matrices = tuple(
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    identities = {
        label: _array_identity(label, value)
        for label, value in zip(("hx", "hz", "lx", "lz"), matrices, strict=True)
    }
    stored = candidate_record.get("matrices")
    if (
        not isinstance(stored, Mapping)
        or any(stored.get(label) != identities[label] for label in identities)
        or stored.get("bundle_sha256") != canonical_sha256(identities)
    ):
        raise ValueError("strict deep candidate matrices changed after queueing")
    return matrices


def _result_without_seal(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result.pop("result_sha256", None)
    return result


def _seal_result(value: Mapping[str, Any]) -> dict[str, Any]:
    result = _result_without_seal(value)
    result["result_sha256"] = canonical_sha256(result)
    return result


def _validate_result(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    digest = result.get("result_sha256")
    if (
        result.get("schema_version") != SCHEMA_VERSION
        or result.get("gate") != RESULT_GATE
        or not _is_sha256(digest)
        or digest != canonical_sha256(_result_without_seal(result))
        or not _is_sha256(result.get("canonical_digest"))
        or result.get("status") not in {SAT, UNSAT, INCOMPLETE}
        or result.get("sector") not in {"X", "Z"}
        or isinstance(result.get("partition_index"), bool)
        or not isinstance(result.get("partition_index"), int)
        or not isinstance(result.get("lane"), Mapping)
        or not _is_sha256(result.get("source_sha256"))
        or not isinstance(result.get("claim_token"), str)
        or isinstance(result.get("attempt"), bool)
        or not isinstance(result.get("attempt"), int)
        or result["attempt"] < 1
        or isinstance(result.get("slice_index"), bool)
        or not isinstance(result.get("slice_index"), int)
        or result["slice_index"] < 0
        or isinstance(result.get("cutoff"), bool)
        or not isinstance(result.get("cutoff"), int)
    ):
        raise ValueError("strict deep unit result is invalid")
    LaneSpec.from_mapping(result["lane"])
    return result


def _checkpoint_identity(
    candidate: Mapping[str, Any],
    lane: Mapping[str, Any],
    unit: Mapping[str, Any],
    *,
    queue_source: Mapping[str, Any],
) -> dict[str, Any]:
    value = {
        "schema_version": SCHEMA_VERSION,
        "gate": UNIT_GATE,
        "deep_source_sha256": _assert_source_unchanged(),
        "ranked_input_sha256": queue_source["ranked_input_sha256"],
        "summary_input_sha256": queue_source["summary_input_sha256"],
        "canonical_digest": candidate["canonical_digest"],
        "candidate_input_sha256": candidate["candidate_input_sha256"],
        "matrix_bundle_sha256": candidate["matrices"]["bundle_sha256"],
        "target_binding_sha256": candidate["target_binding_sha256"],
        "required_distance": candidate["required_distance"],
        "cutoff": candidate["cutoff"],
        "lane": {
            "name": lane["name"],
            "solver": lane["solver"],
            "cardinality_encoding": lane["cardinality_encoding"],
        },
        "sector": unit["sector"],
        "partition_index": unit["partition_index"],
    }
    value["identity_sha256"] = canonical_sha256(value)
    return value


def _solve_claim(
    claim: Mapping[str, Any],
    *,
    paths: DeepPaths,
    config: DeepConfig,
    solve_fn: Callable[..., Mapping[str, Any]] | None = None,
    cancel_event: Any | None = None,
) -> dict[str, Any]:
    """Execute and validate one concrete SAT unit without mutating the queue."""

    _assert_source_unchanged()
    candidate = claim["candidate"]
    lane = claim["lane"]
    unit = claim["unit"]
    hx, hz, lx, lz = _load_candidate_matrices(candidate)
    from evaluation.distance_sat import (
        css_sector_matrices,
        solve_css_sector_sat,
        verify_css_threshold_sat_witness,
    )
    from humanize.exactification_queue import _validate_solver_evidence

    checks, logicals = css_sector_matrices(
        hx, hz, lx, lz, str(unit["sector"]),
    )
    selected_solver = solve_css_sector_sat if solve_fn is None else solve_fn
    slice_index = int(unit["slice_index"])
    timeout_s = float(config.time_slices_s[slice_index])
    identity = _checkpoint_identity(
        candidate, lane, unit, queue_source=claim["queue_source"],
    )
    checkpoint = (
        paths.checkpoints
        / str(candidate["canonical_digest"])
        / str(lane["name"])
        / f"{unit['sector']}-{int(unit['partition_index']):03d}.json"
    )
    started = time.time()
    try:
        evidence = dict(selected_solver(
            checks,
            logicals,
            max_weight=int(candidate["cutoff"]),
            timeout=timeout_s,
            workers=1,
            seed=int(config.seed) + int(unit["attempt"]),
            partition_index=int(unit["partition_index"]),
            sector=str(unit["sector"]),
            cardinality_encoding=str(lane["cardinality_encoding"]),
            solver=str(lane["solver"]),
            checkpoint_path=checkpoint,
            resume=True,
            checkpoint_identity=identity,
            cancel_event=cancel_event,
            termination_grace_s=float(config.termination_grace_s),
        ))
    except Exception as exc:
        return _seal_result({
            "schema_version": SCHEMA_VERSION,
            "gate": RESULT_GATE,
            "status": INCOMPLETE,
            "canonical_digest": candidate["canonical_digest"],
            "lane": {
                "name": lane["name"],
                "solver": lane["solver"],
                "cardinality_encoding": lane["cardinality_encoding"],
            },
            "sector": unit["sector"],
            "partition_index": unit["partition_index"],
            "cutoff": candidate["cutoff"],
            "slice_index": slice_index,
            "attempt": unit["attempt"],
            "claim_token": unit["claim_token"],
            "checkpoint_identity": identity,
            "solver_evidence": {"outcome": "error", "error": str(exc)},
            "source_sha256": _assert_source_unchanged(),
            "started_at": started,
            "finished_at": time.time(),
            "reason": f"solver raised {type(exc).__name__}: {exc}",
            "objective": None,
        })
    try:
        _validate_solver_evidence(
            evidence,
            checks,
            logicals,
            cutoff=int(candidate["cutoff"]),
            sector=str(unit["sector"]),
            partition=int(unit["partition_index"]),
            encoding=str(lane["cardinality_encoding"]),
            checkpoint_identity=identity,
        )
    except ValueError as exc:
        return _seal_result({
            "schema_version": SCHEMA_VERSION,
            "gate": RESULT_GATE,
            "status": INCOMPLETE,
            "canonical_digest": candidate["canonical_digest"],
            "lane": {
                "name": lane["name"],
                "solver": lane["solver"],
                "cardinality_encoding": lane["cardinality_encoding"],
            },
            "sector": unit["sector"],
            "partition_index": unit["partition_index"],
            "cutoff": candidate["cutoff"],
            "slice_index": slice_index,
            "attempt": unit["attempt"],
            "claim_token": unit["claim_token"],
            "checkpoint_identity": identity,
            "solver_evidence": evidence,
            "source_sha256": _assert_source_unchanged(),
            "started_at": started,
            "finished_at": time.time(),
            "reason": f"solver evidence validation failed: {exc}",
            "objective": None,
        })
    outcome = str(evidence.get("outcome", "")).lower()
    status = INCOMPLETE
    reason = f"solver returned {outcome or 'unknown'}"
    objective: int | None = None
    if outcome == "sat":
        failures = verify_css_threshold_sat_witness(evidence, checks, logicals)
        raw_objective = evidence.get("objective")
        if (
            not failures
            and isinstance(raw_objective, int)
            and not isinstance(raw_objective, bool)
            and 1 <= raw_objective <= int(candidate["cutoff"])
        ):
            status = SAT
            objective = int(raw_objective)
            reason = "verified low-weight logical witness"
        else:
            reason = "SAT witness replay failed: " + "; ".join(failures)
    elif (
        outcome == "unsat"
        and evidence.get("decision_complete") is True
        and evidence.get("threshold_infeasible") is True
        and evidence.get("success") is False
        and evidence.get("operator") is None
    ):
        status = UNSAT
        reason = "complete partition UNSAT"
    return _seal_result({
        "schema_version": SCHEMA_VERSION,
        "gate": RESULT_GATE,
        "status": status,
        "canonical_digest": candidate["canonical_digest"],
        "lane": {
            "name": lane["name"],
            "solver": lane["solver"],
            "cardinality_encoding": lane["cardinality_encoding"],
        },
        "sector": unit["sector"],
        "partition_index": unit["partition_index"],
        "cutoff": candidate["cutoff"],
        "slice_index": slice_index,
        "attempt": unit["attempt"],
        "claim_token": unit["claim_token"],
        "checkpoint_identity": identity,
        "solver_evidence": evidence,
        "source_sha256": _assert_source_unchanged(),
        "started_at": started,
        "finished_at": time.time(),
        "reason": reason,
        "objective": objective,
    })


def _refresh_aggregates(queue: dict[str, Any], config: DeepConfig) -> None:
    for candidate in queue["candidates"]:
        for lane in candidate["lanes"]:
            statuses = [unit["status"] for unit in lane["units"]]
            lane["status"] = (
                SAT if SAT in statuses
                else (
                    UNSAT if statuses and all(value == UNSAT for value in statuses)
                    else (
                        RUNNING if RUNNING in statuses
                        else (
                            INCOMPLETE if any(value != PENDING for value in statuses)
                            else PENDING
                        )
                    )
                )
            )
        status, proven = _derived_candidate_status(
            candidate, required_lanes=config.required_proof_lanes,
        )
        candidate["status"] = status
        candidate["proven_lanes"] = proven
        candidate["requires_independent_replay"] = (
            status == PRIMARY_THRESHOLD_PROVEN
        )
        if status in {PRIMARY_THRESHOLD_PROVEN, STRICT_THRESHOLD_PROVEN}:
            candidate["bounds"]["lower"] = int(candidate["required_distance"])
            candidate["bounds"]["lower_source"] = (
                "complete-XZ-first-nonzero-SAT-UNSAT-cover"
            )
        sat_objectives = [
            unit.get("evidence", {}).get("objective")
            for lane in candidate["lanes"]
            for unit in lane["units"]
            if unit.get("status") == SAT and isinstance(unit.get("evidence"), Mapping)
        ]
        sat_objectives = [
            int(value) for value in sat_objectives
            if isinstance(value, int) and not isinstance(value, bool)
        ]
        if sat_objectives:
            new_upper = min(
                int(candidate["bounds"]["upper"]), min(sat_objectives),
            )
            if new_upper < int(candidate["bounds"]["lower"]):
                candidate["bounds"]["bound_conflict"] = {
                    "previous_lower": int(candidate["bounds"]["lower"]),
                    "verified_upper": new_upper,
                    "resolution": "lower-reset-fail-closed",
                }
                candidate["bounds"]["lower"] = 1
                candidate["bounds"]["lower_source"] = (
                    "reset-after-verified-deep-SAT-witness"
                )
            candidate["bounds"]["upper"] = new_upper
            candidate["bounds"]["upper_source"] = "replayed-deep-SAT-witness"
    statuses = [candidate["status"] for candidate in queue["candidates"]]
    if STRICT_THRESHOLD_PROVEN in statuses:
        queue["status"] = STRICT_THRESHOLD_PROVEN
    elif all(status == WITNESS_REJECTED for status in statuses):
        queue["status"] = WITNESS_REJECTED
    else:
        queue["status"] = RUNNING


def _unit_claimable(unit: Mapping[str, Any], config: DeepConfig) -> bool:
    status = unit.get("status")
    if status == PENDING:
        return True
    return bool(
        status == INCOMPLETE
        and isinstance(unit.get("slice_index"), int)
        and (
            unit.get("retry_same_slice") is True
            or int(unit["slice_index"]) < len(config.time_slices_s) - 1
        )
    )


def recover_running_units(
    paths: DeepPaths,
    *,
    now: float | None = None,
) -> dict[str, Any]:
    """Reset orphan RUNNING units after the exclusive sidecar process restarts."""

    timestamp = time.time() if now is None else float(now)
    with _QueueLock(paths):
        queue = validate_queue(paths.queue)
        changed = False
        for candidate in queue["candidates"]:
            for lane in candidate["lanes"]:
                for unit in lane["units"]:
                    if unit["status"] == RUNNING:
                        unit["status"] = INCOMPLETE
                        unit["retry_same_slice"] = True
                        unit["claim_token"] = None
                        unit.pop("claimed_by", None)
                        unit.pop("claimed_at", None)
                        changed = True
        if not changed:
            return queue
        config = DeepConfig.from_json(queue["policy"])
        _refresh_aggregates(queue, config)
        queue["revision"] += 1
        queue["updated_at"] = timestamp
        return _write_queue(paths, queue)


def claim_units(
    paths: DeepPaths,
    *,
    limit: int,
    worker_id: str,
    now: float | None = None,
) -> list[dict[str, Any]]:
    if isinstance(limit, bool) or not isinstance(limit, int) or limit < 1:
        raise ValueError("claim limit must be positive")
    timestamp = time.time() if now is None else float(now)
    with _QueueLock(paths):
        queue = validate_queue(paths.queue)
        if queue["status"] in {STRICT_THRESHOLD_PROVEN, WITNESS_REJECTED}:
            return []
        config = DeepConfig.from_json(queue["policy"])
        choices: list[tuple[tuple[int, int, int, int, int], int, int, int]] = []
        for candidate_index, candidate in enumerate(queue["candidates"]):
            if candidate["status"] in {STRICT_THRESHOLD_PROVEN, WITNESS_REJECTED}:
                continue
            for lane_index, lane in enumerate(candidate["lanes"]):
                for unit_index, unit in enumerate(lane["units"]):
                    if not _unit_claimable(unit, config):
                        continue
                    sector_order = 0 if unit["sector"] == "X" else 1
                    choices.append((
                        (
                            candidate_index,
                            int(unit["slice_index"]),
                            lane_index,
                            sector_order,
                            int(unit["partition_index"]),
                        ),
                        candidate_index,
                        lane_index,
                        unit_index,
                    ))
        claims: list[dict[str, Any]] = []
        for _priority, candidate_index, lane_index, unit_index in sorted(choices)[:limit]:
            candidate = queue["candidates"][candidate_index]
            lane = candidate["lanes"][lane_index]
            unit = lane["units"][unit_index]
            if unit["status"] == INCOMPLETE and not unit["retry_same_slice"]:
                unit["slice_index"] += 1
            unit["retry_same_slice"] = False
            unit["status"] = RUNNING
            unit["attempt"] += 1
            unit["claim_token"] = uuid.uuid4().hex
            unit["claimed_by"] = worker_id
            unit["claimed_at"] = timestamp
            claims.append({
                "candidate": json.loads(json.dumps(candidate)),
                "lane": json.loads(json.dumps(lane)),
                "unit": json.loads(json.dumps(unit)),
                "queue_source": dict(queue["source"]),
            })
        _refresh_aggregates(queue, config)
        if not claims and queue["status"] == RUNNING:
            queue["status"] = INCOMPLETE
        queue["revision"] += 1
        queue["updated_at"] = timestamp
        _write_queue(paths, queue)
        return claims


def _revalidate_terminal_result(
    result: Mapping[str, Any],
    *,
    candidate: Mapping[str, Any],
    lane: Mapping[str, Any],
    unit: Mapping[str, Any],
    queue_source: Mapping[str, Any],
) -> None:
    terminal = result["status"] in {SAT, UNSAT}
    expected_identity = _checkpoint_identity(
        candidate, lane, unit, queue_source=queue_source,
    )
    expected_fields = {
        "canonical_digest": candidate["canonical_digest"],
        "lane": {
            "name": lane["name"],
            "solver": lane["solver"],
            "cardinality_encoding": lane["cardinality_encoding"],
        },
        "sector": unit["sector"],
        "partition_index": unit["partition_index"],
        "cutoff": candidate["cutoff"],
    }
    if any(result.get(key) != value for key, value in expected_fields.items()):
        raise ValueError("strict deep result is not bound to the claimed SAT unit")
    if not terminal:
        return
    if result.get("checkpoint_identity") != expected_identity:
        raise ValueError(
            "terminal strict deep evidence is not bound to the claimed SAT instance"
        )
    evidence = result.get("solver_evidence")
    if not isinstance(evidence, Mapping):
        raise ValueError("terminal strict deep result lacks solver evidence")
    backend = evidence.get("backend")
    if (
        not isinstance(backend, Mapping)
        or backend.get("solver") != lane["solver"]
    ):
        raise ValueError("terminal strict deep result used a different solver")

    from evaluation.distance_sat import (
        css_sector_matrices,
        verify_css_threshold_sat_witness,
    )
    from humanize.exactification_queue import _validate_solver_evidence

    hx, hz, lx, lz = _load_candidate_matrices(candidate)
    checks, logicals = css_sector_matrices(
        hx, hz, lx, lz, str(unit["sector"]),
    )
    _validate_solver_evidence(
        evidence,
        checks,
        logicals,
        cutoff=int(candidate["cutoff"]),
        sector=str(unit["sector"]),
        partition=int(unit["partition_index"]),
        encoding=str(lane["cardinality_encoding"]),
        checkpoint_identity=expected_identity,
    )
    outcome = str(evidence.get("outcome", "")).lower()
    if result["status"] == SAT:
        failures = verify_css_threshold_sat_witness(evidence, checks, logicals)
        objective = evidence.get("objective")
        if (
            outcome != "sat"
            or failures
            or isinstance(objective, bool)
            or not isinstance(objective, int)
            or not 1 <= objective <= int(candidate["cutoff"])
            or result.get("objective") != objective
        ):
            raise ValueError("strict deep SAT result failed independent replay")
    elif (
        outcome != "unsat"
        or evidence.get("decision_complete") is not True
        or evidence.get("threshold_infeasible") is not True
        or evidence.get("success") is not False
        or evidence.get("operator") is not None
        or result.get("objective") is not None
    ):
        raise ValueError("strict deep UNSAT result is not a complete decision")


def complete_unit(
    paths: DeepPaths,
    *,
    worker_id: str,
    result: Mapping[str, Any],
    now: float | None = None,
) -> dict[str, Any]:
    validated_result = _validate_result(result)
    if validated_result["source_sha256"] != _assert_source_unchanged():
        raise ValueError("strict deep result source differs from the live worker")
    timestamp = time.time() if now is None else float(now)
    with _QueueLock(paths):
        queue = validate_queue(paths.queue)
        config = DeepConfig.from_json(queue["policy"])
        candidate = next(
            (
                item for item in queue["candidates"]
                if item["canonical_digest"] == validated_result["canonical_digest"]
            ),
            None,
        )
        if candidate is None:
            raise ValueError("strict deep result candidate is not queued")
        lane = next(
            (
                item for item in candidate["lanes"]
                if item["name"] == validated_result["lane"]["name"]
            ),
            None,
        )
        if (
            lane is None
            or lane["solver"] != validated_result["lane"]["solver"]
            or lane["cardinality_encoding"]
            != validated_result["lane"]["cardinality_encoding"]
        ):
            raise ValueError("strict deep result lane is not queued")
        unit = next(
            (
                item for item in lane["units"]
                if item["sector"] == validated_result["sector"]
                and item["partition_index"] == validated_result["partition_index"]
            ),
            None,
        )
        if (
            unit is None
            or unit["status"] != RUNNING
            or unit.get("claimed_by") != worker_id
            or unit.get("claim_token") != validated_result["claim_token"]
            or unit.get("attempt") != validated_result["attempt"]
            or unit.get("slice_index") != validated_result["slice_index"]
        ):
            raise ValueError("stale strict deep unit result")
        _revalidate_terminal_result(
            validated_result,
            candidate=candidate,
            lane=lane,
            unit=unit,
            queue_source=queue["source"],
        )
        accepted_path = (
            paths.evidence
            / "accepted"
            / str(candidate["canonical_digest"])
            / str(lane["name"])
            / f"{unit['sector']}-{unit['partition_index']:03d}-{validated_result['result_sha256']}.json"
        )
        _write_immutable_json(accepted_path, validated_result)
        unit["status"] = validated_result["status"]
        unit["retry_same_slice"] = False
        unit["claim_token"] = None
        unit.pop("claimed_by", None)
        unit.pop("claimed_at", None)
        unit["evidence"] = {
            "path": str(accepted_path),
            "result_sha256": validated_result["result_sha256"],
            "objective": validated_result.get("objective"),
            "outcome": validated_result.get("solver_evidence", {}).get("outcome"),
        }
        candidate["updated_at"] = timestamp
        _refresh_aggregates(queue, config)
        queue["revision"] += 1
        queue["updated_at"] = timestamp
        return _write_queue(paths, queue)


def run_queue(
    paths: DeepPaths,
    *,
    worker_id: str | None = None,
    solve_fn: Callable[..., Mapping[str, Any]] | None = None,
    stop_event: threading.Event | None = None,
) -> dict[str, Any]:
    """Run/resume the queue with at most four simultaneously live SAT units."""

    _assert_source_unchanged()
    event = threading.Event() if stop_event is None else stop_event
    owner = worker_id or f"deep-{os.getpid()}-{uuid.uuid4().hex}"
    queue = recover_running_units(paths)
    config = DeepConfig.from_json(queue["policy"])
    executor = ThreadPoolExecutor(max_workers=config.max_workers)
    active: dict[Any, tuple[dict[str, Any], threading.Event]] = {}
    try:
        while not event.is_set():
            queue = validate_queue(paths.queue)
            if queue["status"] in {STRICT_THRESHOLD_PROVEN, WITNESS_REJECTED}:
                if queue["status"] == STRICT_THRESHOLD_PROVEN:
                    event.set()
                break
            available = config.max_workers - len(active)
            if available > 0:
                for claim in claim_units(
                    paths, limit=available, worker_id=owner,
                ):
                    unit_event = threading.Event()
                    future = executor.submit(
                        _solve_claim,
                        claim,
                        paths=paths,
                        config=config,
                        solve_fn=solve_fn,
                        cancel_event=unit_event,
                    )
                    active[future] = (claim, unit_event)
            if not active:
                break
            done, _ = wait(
                tuple(active), timeout=0.5, return_when=FIRST_COMPLETED,
            )
            for future in done:
                active.pop(future)
                result = future.result()
                queue = complete_unit(
                    paths, worker_id=owner, result=result,
                )
                completed = next(
                    candidate
                    for candidate in queue["candidates"]
                    if candidate["canonical_digest"] == result["canonical_digest"]
                )
                if completed["status"] == WITNESS_REJECTED:
                    for pending_claim, pending_event in active.values():
                        if (
                            pending_claim["candidate"]["canonical_digest"]
                            == completed["canonical_digest"]
                        ):
                            pending_event.set()
                if queue["status"] == STRICT_THRESHOLD_PROVEN:
                    event.set()
        return validate_queue(paths.queue)
    finally:
        if event.is_set() or active:
            for future, (_claim, unit_event) in active.items():
                unit_event.set()
                future.cancel()
        executor.shutdown(wait=True, cancel_futures=True)
        if active:
            recover_running_units(paths)


__all__ = [
    "DeepConfig",
    "DeepPaths",
    "INCOMPLETE",
    "LaneSpec",
    "PENDING",
    "PRIMARY_THRESHOLD_PROVEN",
    "RUNNING",
    "SAT",
    "STRICT_THRESHOLD_PROVEN",
    "UNSAT",
    "WITNESS_REJECTED",
    "canonical_sha256",
    "claim_units",
    "complete_unit",
    "deep_paths",
    "initialize_queue",
    "queue_status",
    "recover_running_units",
    "run_queue",
    "validate_queue",
]
