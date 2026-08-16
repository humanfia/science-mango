"""Crash-safe strict-FOM discovery sidecar backed by audit_candidate_pool.

The sidecar consumes an already authenticated, deterministically ranked JSONL
and never writes the owning pipeline's state, ledger, outputs, or audit files.
It runs Top100, expands by 400 to Top500, then uses disjoint 500-candidate
batches, stopping as soon as the audited backend emits a ``THRESHOLD_PROVEN`` result.

Scientific imports happen only in the child audit command.  Native thread
limits, affinity, niceness, and the cooperative 24-slot lease are installed
before that command is started.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import math
import os
import signal
import stat
import subprocess
import sys
import threading
import time
import uuid
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, Sequence


SIDECAR_NAME = "stage2-strict-discovery-v1"
PROCESS_KIND = "qcode-stage2-strict-discovery-process"
PROGRESS_GATE = "qcode-stage2-strict-discovery-progress"
PROGRESS_SCHEMA_VERSION = 1
TARGET_MODE = "scalar-fom-strict-v1"
PORTFOLIO_GATE = "qldpc-stage2-strict-discovery-portfolio-v1"
PORTFOLIO_SCHEMA_VERSION = 1
PORTFOLIO_PAYLOAD_KIND = (
    "authenticated-ranked-snapshot-rows-in-portfolio-order"
)

_NATIVE_THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
    "NUMBA_NUM_THREADS",
    "GOTO_NUM_THREADS",
)


class StrictDiscoveryError(RuntimeError):
    """A fail-closed sidecar validation or worker failure."""


@dataclass(frozen=True)
class DiscoveryConfig:
    initial_batch_size: int = 100
    expanded_top: int = 500
    batch_size: int = 500
    candidate_workers: int = 6
    solver_workers: int = 4
    max_total_workers: int = 24
    timeout_s: float = 300.0
    certificate_workers: int = 2
    certificate_solver_workers: int = 6
    certificate_timeout_per_logical_s: float = 3600.0
    certificate_total_timeout_s: float = 86400.0
    verification_timeout_per_logical_s: float = 3600.0
    verification_total_timeout_s: float = 86400.0
    candidate_hard_timeout_s: float | None = None
    termination_grace_s: float = 180.0
    reserve_foreground_cpus: int = 12
    capacity_poll_s: float = 30.0
    nice: int = 10
    cpu_list: tuple[int, ...] | None = None
    seed: int = 0

    def validate(self) -> "DiscoveryConfig":
        integers = {
            "initial_batch_size": self.initial_batch_size,
            "expanded_top": self.expanded_top,
            "batch_size": self.batch_size,
            "candidate_workers": self.candidate_workers,
            "solver_workers": self.solver_workers,
            "max_total_workers": self.max_total_workers,
            "certificate_workers": self.certificate_workers,
            "certificate_solver_workers": self.certificate_solver_workers,
            "reserve_foreground_cpus": self.reserve_foreground_cpus,
            "nice": self.nice,
            "seed": self.seed,
        }
        if any(isinstance(v, bool) or not isinstance(v, int) for v in integers.values()):
            raise ValueError("strict discovery integer settings must be integers")
        if self.initial_batch_size < 1 or self.batch_size < 1:
            raise ValueError("batch sizes must be positive")
        if self.expanded_top <= self.initial_batch_size:
            raise ValueError("expanded_top must exceed initial_batch_size")
        if self.candidate_workers < 1 or self.solver_workers < 1:
            raise ValueError("worker counts must be positive")
        if self.candidate_workers * self.solver_workers > self.max_total_workers:
            raise ValueError("candidate_workers * solver_workers exceeds max_total_workers")
        if self.certificate_workers < 1 or self.certificate_solver_workers < 1:
            raise ValueError("certificate worker counts must be positive")
        if self.certificate_workers * self.certificate_solver_workers > self.max_total_workers:
            raise ValueError("certificate worker budget exceeds max_total_workers")
        if self.max_total_workers != 24:
            raise ValueError("strict discovery requires max_total_workers=24")
        if self.reserve_foreground_cpus < 12:
            raise ValueError("reserve_foreground_cpus must be at least 12")
        if not 0 <= self.nice <= 19:
            raise ValueError("nice must be between 0 and 19")
        for name, value in (
            ("timeout_s", self.timeout_s),
            ("capacity_poll_s", self.capacity_poll_s),
            ("termination_grace_s", self.termination_grace_s),
            ("certificate_timeout_per_logical_s", self.certificate_timeout_per_logical_s),
            ("certificate_total_timeout_s", self.certificate_total_timeout_s),
            ("verification_timeout_per_logical_s", self.verification_timeout_per_logical_s),
            ("verification_total_timeout_s", self.verification_total_timeout_s),
        ):
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError(f"{name} must be numeric")
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ValueError(f"{name} must be positive and finite")
        if self.candidate_hard_timeout_s is not None:
            value = self.candidate_hard_timeout_s
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError("candidate_hard_timeout_s must be numeric or null")
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ValueError("candidate_hard_timeout_s must be positive and finite")
        if self.termination_grace_s < 180:
            raise ValueError("termination_grace_s must be at least 180")
        if self.cpu_list is not None:
            if len(self.cpu_list) < self.max_total_workers:
                raise ValueError("cpu_list must contain at least max_total_workers CPUs")
            if len(set(self.cpu_list)) != len(self.cpu_list) or min(self.cpu_list) < 0:
                raise ValueError("cpu_list must contain distinct non-negative CPUs")
        return self

    @classmethod
    def from_json(cls, source: Path | str | Mapping[str, Any]) -> "DiscoveryConfig":
        if isinstance(source, Mapping):
            document: Any = dict(source)
        else:
            document = _read_json(Path(source), label="strict discovery config")
        raw = document.get("discovery", document) if isinstance(document, Mapping) else None
        if not isinstance(raw, Mapping):
            raise ValueError("strict discovery config must contain an object")
        allowed = set(cls.__dataclass_fields__)
        unknown = set(raw) - allowed
        if unknown:
            raise ValueError("unknown strict discovery settings: " + ", ".join(sorted(unknown)))
        values = dict(raw)
        if values.get("cpu_list") is not None:
            values["cpu_list"] = parse_cpu_list(values["cpu_list"])
        return cls(**values).validate()

    def as_dict(self) -> dict[str, Any]:
        value = asdict(self.validate())
        value["cpu_list"] = list(self.cpu_list) if self.cpu_list is not None else None
        return value


@dataclass(frozen=True)
class SidecarPaths:
    repo: Path
    run_root: Path
    root: Path
    process: Path
    lock: Path
    log: Path
    progress: Path
    batches: Path


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


_CLI_SOURCE_PATH = Path(__file__).resolve()
_CLI_SOURCE_SHA256 = _file_sha256(_CLI_SOURCE_PATH)


def _assert_cli_source_unchanged() -> str:
    current = _file_sha256(_CLI_SOURCE_PATH)
    if current != _CLI_SOURCE_SHA256:
        raise StrictDiscoveryError("strict discovery CLI source changed while running")
    return current


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    before = path.lstat()
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        raise ValueError(f"{label} must be a regular non-symlink file")
    payload = path.read_bytes()
    after = path.lstat()
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    ):
        raise ValueError(f"{label} changed while reading")
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"{label} is malformed JSON") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain an object")
    return value


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    try:
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(temporary, flags, 0o600)
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    _atomic_write(path, _canonical_bytes(dict(value)) + b"\n")


def parse_cpu_list(value: Any) -> tuple[int, ...]:
    if isinstance(value, (list, tuple)):
        if any(isinstance(item, bool) or not isinstance(item, int) for item in value):
            raise ValueError("cpu_list entries must be integers")
        cpus = set(value)
    elif isinstance(value, str):
        cpus: set[int] = set()
        for item in value.split(","):
            item = item.strip()
            if not item:
                continue
            if "-" in item:
                left, right = (int(part) for part in item.split("-", 1))
                if right < left:
                    raise ValueError("cpu_list range is descending")
                cpus.update(range(left, right + 1))
            else:
                cpus.add(int(item))
    else:
        raise ValueError("cpu_list must be a list or cpuset string")
    if not cpus or min(cpus) < 0:
        raise ValueError("cpu_list must contain non-negative CPUs")
    return tuple(sorted(cpus))


def sidecar_paths(repo_dir: Path | str, run_id: str, *, create: bool = False) -> SidecarPaths:
    if not run_id or any(char not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.-" for char in run_id):
        raise ValueError("unsafe run_id")
    repo = Path(repo_dir).expanduser().resolve(strict=True)
    pipelines = (repo / "results" / "humanize" / "pipelines").resolve(strict=True)
    run_root = (pipelines / run_id).resolve(strict=True)
    run_root.relative_to(pipelines)
    root = run_root / "sidecars" / SIDECAR_NAME
    if create:
        root.mkdir(parents=True, mode=0o700, exist_ok=True)
    resolved = root.resolve(strict=create)
    resolved.relative_to(run_root)
    return SidecarPaths(
        repo=repo,
        run_root=run_root,
        root=resolved,
        process=resolved / "process.json",
        lock=resolved / "process.lock",
        log=resolved / "worker.log",
        progress=resolved / "progress.json",
        batches=resolved / "batches",
    )


def _seal_progress(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result.pop("progress_sha256", None)
    result["progress_sha256"] = _sha256(result)
    return result


def validate_progress(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    unsigned = dict(result)
    digest = unsigned.pop("progress_sha256", None)
    if (
        result.get("schema_version") != PROGRESS_SCHEMA_VERSION
        or result.get("gate") != PROGRESS_GATE
        or digest != _sha256(unsigned)
        or not isinstance(result.get("source"), Mapping)
        or not isinstance(result.get("batches"), list)
        or isinstance(result.get("next_row"), bool)
        or not isinstance(result.get("next_row"), int)
        or result["next_row"] < 0
        or result.get("status") not in {
            "RUNNING",
            "STRICT_THRESHOLD_PROVEN",
            "EXHAUSTED",
            "INCOMPLETE",
            "FAILED",
        }
    ):
        raise ValueError("strict discovery progress seal is invalid")
    return result


def _load_progress(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return validate_progress(_read_json(path, label="strict discovery progress"))


def _write_progress(path: Path, value: Mapping[str, Any]) -> dict[str, Any]:
    sealed = _seal_progress(value)
    validate_progress(sealed)
    _atomic_write_json(path, sealed)
    return sealed


def _source_identity(path: Path) -> dict[str, Any]:
    before = path.lstat()
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        raise ValueError("ranked input must be a regular non-symlink file")
    digest = _file_sha256(path)
    after = path.lstat()
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    ):
        raise ValueError("ranked input changed while hashing")
    return {
        "path": str(path.resolve()),
        "sha256": digest,
        "device": int(after.st_dev),
        "inode": int(after.st_ino),
        "bytes": int(after.st_size),
        "mtime_ns": int(after.st_mtime_ns),
    }



def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _confined_regular_path(
    raw: Path | str,
    *,
    run_root: Path,
    label: str,
) -> Path:
    value = Path(raw).expanduser()
    if value.is_symlink():
        raise ValueError(f"{label} may not be a symlink")
    resolved = value.resolve(strict=True)
    if not resolved.is_file():
        raise ValueError(f"{label} must be a regular file")
    try:
        resolved.relative_to(run_root)
    except ValueError as exc:
        raise ValueError(f"{label} escapes the pipeline run") from exc
    return resolved


def load_portfolio_manifest(
    portfolio_manifest: Path | str,
    *,
    paths: SidecarPaths,
    ranked_input: Path | str | None = None,
) -> tuple[dict[str, Any], Path, dict[str, Any]]:
    manifest_path = _confined_regular_path(
        portfolio_manifest,
        run_root=paths.run_root,
        label="portfolio manifest",
    )
    _assert_cli_source_unchanged()
    manifest = _read_json(manifest_path, label="strict discovery portfolio")
    unsigned = dict(manifest)
    seal = unsigned.pop("portfolio_sha256", None)
    producer = manifest.get("producer")
    from . import strict_discovery_ranking as ranking_producer

    ranking_source = Path(ranking_producer.__file__).resolve(strict=True)
    expected_ranking_source = _CLI_SOURCE_PATH.with_name(
        "strict_discovery_ranking.py"
    ).resolve(strict=True)
    current_ranking_sha256 = _file_sha256(ranking_source)
    ranked = manifest.get("ranked_input")
    source = manifest.get("source")
    items = manifest.get("items")
    batches = manifest.get("batches")
    if (
        manifest.get("schema_version") != PORTFOLIO_SCHEMA_VERSION
        or manifest.get("gate") != PORTFOLIO_GATE
        or manifest.get("target_mode") != TARGET_MODE
        or manifest.get("publication_certificate") is not False
        or manifest.get("pipeline_promotion") is not False
        or not isinstance(producer, Mapping)
        or producer.get("module") != "humanize.strict_discovery_ranking"
        or not _is_sha256(producer.get("source_sha256"))
        or ranking_source != expected_ranking_source
        or producer.get("source_sha256") != current_ranking_sha256
        or getattr(ranking_producer, "_RANKING_SOURCE_SHA256", None)
        != current_ranking_sha256
        or not _is_sha256(seal)
        or seal != _sha256(unsigned)
        or not isinstance(ranked, Mapping)
        or ranked.get("payload_kind") != PORTFOLIO_PAYLOAD_KIND
        or not isinstance(source, Mapping)
        or not isinstance(items, list)
        or not isinstance(batches, list)
    ):
        raise ValueError("strict discovery portfolio seal/schema is invalid")
    ranked_path = _confined_regular_path(
        str(ranked.get("path")),
        run_root=paths.run_root,
        label="portfolio ranked input",
    )
    if ranked_input is not None:
        supplied = _confined_regular_path(
            ranked_input,
            run_root=paths.run_root,
            label="ranked input",
        )
        if supplied != ranked_path:
            raise ValueError("ranked input differs from the sealed portfolio")
    ranked_identity = _source_identity(ranked_path)
    if (
        ranked.get("path") != str(ranked_path)
        or ranked.get("sha256") != ranked_identity["sha256"]
        or ranked.get("bytes") != ranked_identity["bytes"]
        or isinstance(ranked.get("rows"), bool)
        or not isinstance(ranked.get("rows"), int)
        or ranked.get("rows") != len(items)
    ):
        raise ValueError("portfolio ranked input identity is invalid")

    item_digests: list[str] = []
    for rank, raw_item in enumerate(items, start=1):
        if not isinstance(raw_item, Mapping):
            raise ValueError("portfolio item is malformed")
        digest = raw_item.get("canonical_digest")
        n, k = raw_item.get("n"), raw_item.get("k")
        required = raw_item.get("d_req")
        if (
            not _is_sha256(digest)
            or raw_item.get("portfolio_rank") != rank
            or raw_item.get("scheduling_only") is not True
            or any(
                isinstance(value, bool)
                or not isinstance(value, int)
                or value < 1
                for value in (n, k, required)
            )
            or raw_item.get("required_distance") != required
            or raw_item.get("cutoff") != required - 1
            or k * required * required <= 12 * n
            or (
                required > 1
                and k * (required - 1) * (required - 1) > 12 * n
            )
        ):
            raise ValueError("portfolio item strict target binding is invalid")
        item_digests.append(str(digest))
    if len(set(item_digests)) != len(item_digests):
        raise ValueError("portfolio contains duplicate candidates")
    flattened: list[str] = []
    for sequence, raw_batch in enumerate(batches):
        if not isinstance(raw_batch, Mapping):
            raise ValueError("portfolio batch is malformed")
        digests = raw_batch.get("digests")
        if (
            raw_batch.get("sequence") != sequence
            or not isinstance(digests, list)
            or raw_batch.get("count") != len(digests)
            or any(not _is_sha256(value) for value in digests)
        ):
            raise ValueError("portfolio batch binding is invalid")
        flattened.extend(str(value) for value in digests)
    if flattened != item_digests:
        raise ValueError("portfolio batches do not replay the item order")

    required_source = (
        "ledger_path",
        "ledger_generation",
        "ledger_cursor",
        "snapshot_identity_sha256",
        "manifest_path",
        "manifest_file_sha256",
        "manifest_sha256",
    )
    if (
        any(name not in source for name in required_source)
        or not _is_sha256(source.get("snapshot_identity_sha256"))
        or not _is_sha256(source.get("manifest_file_sha256"))
        or not _is_sha256(source.get("manifest_sha256"))
    ):
        raise ValueError("portfolio source provenance is incomplete")
    _confined_regular_path(
        str(source["ledger_path"]),
        run_root=paths.run_root,
        label="portfolio Stage 2 ledger",
    )
    _confined_regular_path(
        str(source["manifest_path"]),
        run_root=paths.run_root,
        label="portfolio ranked snapshot manifest",
    )
    manifest_identity = _source_identity(manifest_path)
    bound_source = {
        "portfolio_manifest_path": str(manifest_path),
        "portfolio_manifest_file_sha256": manifest_identity["sha256"],
        "portfolio_sha256": seal,
        "ranked_input": ranked_identity,
        "stage2_source": dict(source),
    }
    return manifest, ranked_path, bound_source


def validate_live_portfolio_source(
    manifest: Mapping[str, Any],
    *,
    paths: SidecarPaths,
    candidate_digests: Iterable[str],
) -> dict[str, Any]:
    """Fence a batch against current foreground Stage 2 ownership at launch."""

    source = manifest.get("source")
    if not isinstance(source, Mapping):
        raise ValueError("portfolio source provenance is absent")
    ledger_path = _confined_regular_path(
        str(source.get("ledger_path")),
        run_root=paths.run_root,
        label="live Stage 2 ledger",
    )
    snapshot_manifest_path = _confined_regular_path(
        str(source.get("manifest_path")),
        run_root=paths.run_root,
        label="live ranked snapshot manifest",
    )
    if _file_sha256(snapshot_manifest_path) != source.get("manifest_file_sha256"):
        raise StrictDiscoveryError("ranked snapshot manifest changed after portfolio creation")
    snapshot_manifest = _read_json(
        snapshot_manifest_path,
        label="live ranked snapshot manifest",
    )
    if snapshot_manifest.get("manifest_sha256") != source.get("manifest_sha256"):
        raise StrictDiscoveryError("ranked snapshot manifest seal changed")

    ledger = _read_json(ledger_path, label="live Stage 2 selection ledger")
    from evaluation.selection_ledger import validate_selection_ledger

    validated = validate_selection_ledger(
        ledger,
        binding_sha256=str(ledger.get("binding_sha256")),
        snapshot_identity_sha256_value=str(
            ledger.get("snapshot_identity_sha256")
        ),
        snapshot_rows=ledger.get("snapshot_rows"),
        eligible_rows=ledger.get("eligible_rows"),
    )
    if (
        validated.get("snapshot_identity_sha256")
        != source.get("snapshot_identity_sha256")
        or validated.get("generation") != source.get("ledger_generation")
        or not isinstance(validated.get("cursor"), int)
        or validated["cursor"] < int(source.get("portfolio_cursor", source["ledger_cursor"]))
    ):
        raise StrictDiscoveryError("live Stage 2 source no longer extends the portfolio source")
    blocked = {str(value) for value in validated.get("committed_digests", [])}
    pending = validated.get("pending")
    if isinstance(pending, Mapping):
        page = (
            pending.get("page")
            if isinstance(pending.get("page"), Mapping)
            else pending
        )
        blocked.update(str(value) for value in page.get("selected_digests", []))
    requested = {str(value) for value in candidate_digests}
    overlap = sorted(requested.intersection(blocked))
    return {
        "ledger_progress_sha256": validated.get("progress_sha256"),
        "ledger_last_ack_sha256": validated.get("last_ack_sha256"),
        "ledger_cursor": validated.get("cursor"),
        "ledger_generation": validated.get("generation"),
        "pending_page_sha256": (
            pending.get("page_sha256") if isinstance(pending, Mapping) else None
        ),
        "checked_candidates": len(requested),
        "overlap": bool(overlap),
        "blocked_digests": overlap,
        "check_scope": "pre-launch; sidecar never reserves or mutates foreground ownership",
    }

def _write_batch(source: Path, destination: Path, *, start: int, limit: int) -> int:
    rows: list[bytes] = []
    before_source = source.lstat()
    if stat.S_ISLNK(before_source.st_mode) or not stat.S_ISREG(before_source.st_mode):
        raise ValueError("ranked input must remain a regular non-symlink file")
    with source.open("rb") as stream:
        for index, raw in enumerate(stream):
            if index < start:
                continue
            if len(rows) >= limit:
                break
            if not raw.endswith(b"\n"):
                raise ValueError("ranked input contains a partial JSONL row")
            try:
                value = json.loads(raw)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ValueError(f"ranked input row {index + 1} is malformed") from exc
            if not isinstance(value, dict):
                raise ValueError(f"ranked input row {index + 1} is not an object")
            rows.append(_canonical_bytes(value) + b"\n")
    after_source = source.lstat()
    if (
        before_source.st_dev,
        before_source.st_ino,
        before_source.st_size,
        before_source.st_mtime_ns,
    ) != (
        after_source.st_dev,
        after_source.st_ino,
        after_source.st_size,
        after_source.st_mtime_ns,
    ):
        raise ValueError("ranked input changed while reading a batch")
    if rows:
        payload = b"".join(rows)
        if destination.exists():
            before = destination.lstat()
            if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
                raise ValueError("existing batch input is not a safe regular file")
            if destination.read_bytes() != payload:
                raise ValueError("existing batch input differs from deterministic replay")
        else:
            _atomic_write(destination, payload)
    return len(rows)



def _write_selected_batch(
    source: Path,
    destination: Path,
    *,
    source_rows: Sequence[int],
) -> int:
    indexes = tuple(source_rows)
    if (
        any(isinstance(index, bool) or not isinstance(index, int) or index < 0 for index in indexes)
        or tuple(sorted(set(indexes))) != indexes
    ):
        raise ValueError("selected portfolio source rows are invalid")
    if not indexes:
        return 0
    wanted = set(indexes)
    rows: list[bytes] = []
    before_source = source.lstat()
    if stat.S_ISLNK(before_source.st_mode) or not stat.S_ISREG(before_source.st_mode):
        raise ValueError("ranked input must remain a regular non-symlink file")
    with source.open("rb") as stream:
        for index, raw in enumerate(stream):
            if index > indexes[-1]:
                break
            if index not in wanted:
                continue
            if not raw.endswith(b"\n"):
                raise ValueError("ranked input contains a partial JSONL row")
            try:
                value = json.loads(raw)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ValueError(f"ranked input row {index + 1} is malformed") from exc
            if not isinstance(value, dict):
                raise ValueError(f"ranked input row {index + 1} is not an object")
            rows.append(_canonical_bytes(value) + b"\n")
    after_source = source.lstat()
    if (
        before_source.st_dev,
        before_source.st_ino,
        before_source.st_size,
        before_source.st_mtime_ns,
    ) != (
        after_source.st_dev,
        after_source.st_ino,
        after_source.st_size,
        after_source.st_mtime_ns,
    ):
        raise ValueError("ranked input changed while reading selected rows")
    if len(rows) != len(indexes):
        raise ValueError("ranked input ended before selected portfolio rows")
    payload = b"".join(rows)
    if destination.exists():
        metadata = destination.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise ValueError("existing batch input is not a safe regular file")
        if destination.read_bytes() != payload:
            raise ValueError("existing batch input differs from sealed active batch")
    else:
        _atomic_write(destination, payload)
    return len(rows)

def build_audit_argv(
    *,
    python_executable: str,
    paths: SidecarPaths,
    config: DiscoveryConfig,
    batch_index: int,
    count: int,
) -> list[str]:
    batch_root = paths.batches / f"batch-{batch_index:04d}"
    argv = [
        python_executable,
        str(paths.repo / "scripts" / "audit_candidate_pool.py"),
        str(batch_root / "input.jsonl"),
        "--top", str(count),
        "--target-mode", TARGET_MODE,
        "--state-dir", str(batch_root / "state"),
        "--ranked-output", str(batch_root / "ranked.jsonl"),
        "--summary-output", str(batch_root / "summary.json"),
        "--selection-ledger", str(batch_root / "selection-ledger.json"),
        "--timeout", str(config.timeout_s),
        "--candidate-workers", str(config.candidate_workers),
        "--solver-workers", str(config.solver_workers),
        "--max-total-workers", str(config.max_total_workers),
        "--certificate-workers", str(config.certificate_workers),
        "--certificate-solver-workers", str(config.certificate_solver_workers),
        "--certificate-timeout-per-logical", str(config.certificate_timeout_per_logical_s),
        "--certificate-total-timeout", str(config.certificate_total_timeout_s),
        "--verification-timeout-per-logical", str(config.verification_timeout_per_logical_s),
        "--verification-total-timeout", str(config.verification_total_timeout_s),
        "--seed", str(config.seed),
        "--resume",
        "--certify",
        "--hard-wall-termination-grace", str(config.termination_grace_s),
    ]
    if config.candidate_hard_timeout_s is not None:
        argv.extend(["--candidate-hard-timeout", str(config.candidate_hard_timeout_s)])
    return argv


def _ranked_wins(path: Path) -> list[dict[str, Any]]:
    wins: list[dict[str, Any]] = []
    if path.is_symlink() or not path.is_file():
        return wins
    with path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"ranked output row {line_number} is malformed") from exc
            audit = row.get("campaign_audit") if isinstance(row, Mapping) else None
            certificate = (
                audit.get("certificate") if isinstance(audit, Mapping) else None
            )
            if (
                isinstance(audit, Mapping)
                and audit.get("status") == "THRESHOLD_PROVEN"
                and isinstance(certificate, Mapping)
                and certificate.get("attempted") is True
                and certificate.get("certificate_exact") is True
                and certificate.get("certificate_passed") is True
                and certificate.get("verification_attempted") is True
                and certificate.get("verification_passed") is True
            ):
                wins.append({
                    "canonical_digest": audit.get("canonical_digest"),
                    "status": "STRICT_THRESHOLD_PROVEN",
                    "backend_status": "THRESHOLD_PROVEN",
                    "publication_certificate": False,
                    "pipeline_promotion": False,
                    "certificate_sha256": certificate.get(
                        "certificate_sha256"
                    ),
                    "row": line_number,
                })
    return wins



def _complete_unresolved_batch(
    ranked_path: Path,
    summary_path: Path,
    *,
    expected_rows: int,
) -> tuple[bool, bool, dict[str, int]]:
    """Recognize a scientifically complete no-win batch despite backend exit 2."""

    if not summary_path.is_file() or summary_path.is_symlink():
        return False, False, {}
    summary = _read_json(summary_path, label="strict discovery batch summary")
    selected = summary.get("selected_candidates")
    accounting_names = (
        "canonical_duplicates_skipped",
        "known_codes_skipped",
        "unsupported_candidates_skipped",
        "canonicalization_errors",
        "structural_unresolved_candidates",
        "unscanned_eligible_candidates",
        "certificate_operational_errors",
    )
    accounting = {name: summary.get(name) for name in accounting_names}
    if (
        summary.get("target_mode") != TARGET_MODE
        or summary.get("top") != expected_rows
        or summary.get("selection_exhausted") is not True
        or isinstance(selected, bool)
        or not isinstance(selected, int)
        or selected < 0
        or any(
            isinstance(value, bool)
            or not isinstance(value, int)
            or value < 0
            for value in accounting.values()
        )
        or selected
        + accounting["canonical_duplicates_skipped"]
        + accounting["known_codes_skipped"]
        != expected_rows
        or accounting["unsupported_candidates_skipped"] != 0
        or accounting["canonicalization_errors"] != 0
        or accounting["structural_unresolved_candidates"] != 0
        or accounting["unscanned_eligible_candidates"] != 0
        or accounting["certificate_operational_errors"] != 0
    ):
        return False, False, {}
    counts: dict[str, int] = {}
    audited = 0
    selected_rows = 0
    if ranked_path.is_symlink() or not ranked_path.is_file():
        return False, False, {}
    with ranked_path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(
                    f"ranked output row {line_number} is malformed"
                ) from exc
            if not isinstance(row, Mapping) or row.get("campaign_selected") is not True:
                continue
            selected_rows += 1
            audit = row.get("campaign_audit")
            if not isinstance(audit, Mapping):
                return False, False, {}
            status = str(audit.get("status"))
            counts[status] = counts.get(status, 0) + 1
            audited += 1
    allowed = {"REJECTED", "UNRESOLVED"}
    complete = (
        selected_rows == selected
        and audited == selected
        and set(counts).issubset(allowed)
        and "ERROR" not in counts
    )
    has_unresolved = counts.get("UNRESOLVED", 0) > 0
    return complete, has_unresolved, counts

def _native_thread_limits() -> None:
    for name in _NATIVE_THREAD_ENV:
        os.environ[name] = "1"


def _select_cpus(config: DiscoveryConfig) -> tuple[tuple[int, ...], tuple[int, ...]]:
    try:
        allowed = tuple(sorted(os.sched_getaffinity(0)))
    except (AttributeError, OSError):
        allowed = tuple(range(os.cpu_count() or 1))
    selected = config.cpu_list or allowed[-config.max_total_workers :]
    if len(selected) < config.max_total_workers or not set(selected).issubset(allowed):
        raise ValueError("at least 24 allowed CPUs are required for strict discovery")
    return allowed, tuple(selected)


def _apply_resources(config: DiscoveryConfig, selected: Sequence[int]) -> None:
    _native_thread_limits()
    if hasattr(os, "sched_setaffinity"):
        os.sched_setaffinity(0, set(selected))
    if hasattr(os, "setpriority"):
        os.setpriority(os.PRIO_PROCESS, 0, config.nice)
    elif config.nice:
        os.nice(config.nice)


def run_discovery(
    *,
    paths: SidecarPaths,
    portfolio_manifest: Path | str,
    config: DiscoveryConfig,
    ranked_input: Path | str | None = None,
    python_executable: str = sys.executable,
    run_command: Callable[..., Any] = subprocess.run,
    stop_requested: Callable[[], bool] = lambda: False,
    live_source_validator: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Run/resume disjoint progressive batches and return sealed progress."""

    config = config.validate()
    manifest, source_path, source = load_portfolio_manifest(
        portfolio_manifest,
        paths=paths,
        ranked_input=ranked_input,
    )
    items = manifest["items"]
    validator = (
        validate_live_portfolio_source
        if live_source_validator is None
        else live_source_validator
    )
    paths.batches.mkdir(parents=True, exist_ok=True)
    progress = _load_progress(paths.progress)
    config_sha = _sha256(config.as_dict())
    if progress is None:
        progress = _write_progress(paths.progress, {
            "schema_version": PROGRESS_SCHEMA_VERSION,
            "gate": PROGRESS_GATE,
            "status": "RUNNING",
            "source": source,
            "config": config.as_dict(),
            "config_sha256": config_sha,
            "next_row": 0,
            "batches": [],
            "wins": [],
            "foreground_skips": [],
            "updated_at": time.time(),
        })
    elif progress["source"] != source or progress.get("config_sha256") != config_sha:
        raise ValueError("ranked input or discovery policy changed after progress was created")
    if progress["status"] in {
        "STRICT_THRESHOLD_PROVEN",
        "EXHAUSTED",
        "INCOMPLETE",
    }:
        return progress

    def terminal_status() -> str:
        if any(
            isinstance(batch, Mapping) and batch.get("disposition") == "DEFERRED"
            for batch in progress["batches"]
        ):
            return "INCOMPLETE"
        return "EXHAUSTED"

    while not stop_requested():
        batch_index = len(progress["batches"])
        limit = (
            config.initial_batch_size
            if batch_index == 0
            else (
                config.expanded_top - config.initial_batch_size
                if batch_index == 1
                else config.batch_size
            )
        )
        active_raw = progress.get("active_batch")
        if active_raw is not None:
            if not isinstance(active_raw, Mapping):
                raise StrictDiscoveryError("sealed active batch is malformed")
            active = dict(active_raw)
            batch_root = paths.batches / f"batch-{batch_index:04d}"
            expected_input = (batch_root / "input.jsonl").resolve()
            input_path = _confined_regular_path(
                str(active.get("input_path")),
                run_root=paths.run_root,
                label="sealed active batch input",
            )
            source_rows = active.get("selected_source_rows")
            selected_ranks = active.get("selected_portfolio_ranks")
            selected_digests = active.get("selected_digests")
            skipped = active.get("skipped_foreground_owned_digests")
            start_row = active.get("manifest_start_row")
            next_row = active.get("manifest_next_row")
            count = active.get("rows")
            argv_raw = active.get("argv")
            if (
                active.get("batch_index") != batch_index
                or input_path != expected_input
                or isinstance(start_row, bool)
                or not isinstance(start_row, int)
                or start_row != progress["next_row"]
                or isinstance(next_row, bool)
                or not isinstance(next_row, int)
                or not start_row < next_row <= len(items)
                or isinstance(count, bool)
                or not isinstance(count, int)
                or not 0 < count <= limit
                or not isinstance(source_rows, list)
                or len(source_rows) != count
                or any(
                    isinstance(row, bool) or not isinstance(row, int)
                    for row in source_rows
                )
                or source_rows != sorted(set(source_rows))
                or source_rows[0] < start_row
                or source_rows[-1] >= next_row
                or not isinstance(selected_ranks, list)
                or not isinstance(selected_digests, list)
                or len(selected_ranks) != count
                or len(selected_digests) != count
                or not isinstance(skipped, list)
                or active.get("skipped_foreground_owned_count") != len(skipped)
                or active.get("skipped_foreground_owned_sha256") != _sha256(skipped)
                or not isinstance(argv_raw, list)
                or not argv_raw
                or any(not isinstance(value, str) for value in argv_raw)
                or active.get("input_sha256") != _file_sha256(input_path)
            ):
                raise StrictDiscoveryError("sealed active batch identity is invalid")
            expected_digests = [
                items[row]["canonical_digest"] for row in source_rows
            ]
            expected_ranks = [items[row]["portfolio_rank"] for row in source_rows]
            argv = list(argv_raw)
            if (
                selected_digests != expected_digests
                or selected_ranks != expected_ranks
                or argv != build_audit_argv(
                    python_executable=argv[0],
                    paths=paths,
                    config=config,
                    batch_index=batch_index,
                    count=count,
                )
                or not isinstance(active.get("live_source"), Mapping)
            ):
                raise StrictDiscoveryError("sealed active batch does not bind the portfolio")
        else:
            start_row = int(progress["next_row"])
            if start_row >= len(items):
                progress = _write_progress(paths.progress, {
                    **progress,
                    "status": terminal_status(),
                    "updated_at": time.time(),
                })
                return progress
            manifest_identity = _source_identity(
                Path(source["portfolio_manifest_path"])
            )
            if manifest_identity["sha256"] != source["portfolio_manifest_file_sha256"]:
                raise StrictDiscoveryError("portfolio manifest changed while running")
            remaining_digests = [
                str(item["canonical_digest"]) for item in items[start_row:]
            ]
            live_source = validator(
                manifest,
                paths=paths,
                candidate_digests=remaining_digests,
            )
            if not isinstance(live_source, Mapping):
                raise StrictDiscoveryError("live Stage 2 source check is malformed")
            blocked_raw = live_source.get("blocked_digests", [])
            if (
                not isinstance(blocked_raw, list)
                or any(not _is_sha256(value) for value in blocked_raw)
            ):
                raise StrictDiscoveryError("live Stage 2 blocked digest list is malformed")
            blocked = set(blocked_raw)
            if not blocked.issubset(set(remaining_digests)):
                raise StrictDiscoveryError("live Stage 2 reported an unknown blocked candidate")

            source_rows: list[int] = []
            selected_ranks: list[int] = []
            selected_digests: list[str] = []
            skipped: list[str] = []
            cursor = start_row
            while cursor < len(items) and len(source_rows) < limit:
                item = items[cursor]
                digest = str(item["canonical_digest"])
                if digest in blocked:
                    skipped.append(digest)
                else:
                    source_rows.append(cursor)
                    selected_ranks.append(int(item["portfolio_rank"]))
                    selected_digests.append(digest)
                cursor += 1
            if not source_rows:
                skip_record = {
                    "manifest_start_row": start_row,
                    "manifest_next_row": cursor,
                    "skipped_foreground_owned_count": len(skipped),
                    "skipped_foreground_owned_digests": skipped,
                    "skipped_foreground_owned_sha256": _sha256(skipped),
                    "live_source": dict(live_source),
                    "recorded_at": time.time(),
                }
                progress = _write_progress(paths.progress, {
                    **progress,
                    "status": terminal_status(),
                    "next_row": cursor,
                    "foreground_skips": [
                        *progress.get("foreground_skips", []),
                        skip_record,
                    ],
                    "updated_at": time.time(),
                })
                return progress

            batch_root = paths.batches / f"batch-{batch_index:04d}"
            batch_root.mkdir(parents=True, exist_ok=True)
            input_path = batch_root / "input.jsonl"
            count = _write_selected_batch(
                source_path,
                input_path,
                source_rows=source_rows,
            )
            if count != len(source_rows):
                raise StrictDiscoveryError(
                    "portfolio ranked input ended before selected source rows"
                )
            argv = build_audit_argv(
                python_executable=python_executable,
                paths=paths,
                config=config,
                batch_index=batch_index,
                count=count,
            )
            active = {
                "batch_index": batch_index,
                "manifest_start_row": start_row,
                "manifest_next_row": cursor,
                "selected_source_rows": source_rows,
                "selected_portfolio_ranks": selected_ranks,
                "selected_digests": selected_digests,
                "rows": count,
                "input_path": str(input_path.resolve()),
                "input_sha256": _file_sha256(input_path),
                "argv": argv,
                "started_at": time.time(),
                "attempts": 0,
                "live_source": dict(live_source),
                "skipped_foreground_owned_count": len(skipped),
                "skipped_foreground_owned_digests": skipped,
                "skipped_foreground_owned_sha256": _sha256(skipped),
            }

        active = {**active, "attempts": int(active.get("attempts", 0)) + 1}
        progress = _write_progress(paths.progress, {
            **progress,
            "status": "RUNNING",
            "active_batch": active,
            "updated_at": time.time(),
        })
        completed = run_command(argv, cwd=paths.repo, shell=False, check=False)
        returncode = int(getattr(completed, "returncode", completed))
        ranked_output = batch_root / "ranked.jsonl"
        wins = _ranked_wins(ranked_output)
        summary_output = batch_root / "summary.json"
        complete_no_error, has_unresolved, deferred_statuses = (
            _complete_unresolved_batch(
                ranked_output,
                summary_output,
                expected_rows=count,
            )
        )
        batch = {
            **active,
            "ranked_output": str(ranked_output),
            "summary_output": str(summary_output),
            "disposition": (
                "PROVEN"
                if wins
                else ("DEFERRED" if has_unresolved else "COMPLETED")
            ),
            "status_counts": deferred_statuses,
            "returncode": returncode,
            "wins": wins,
            "completed_at": time.time(),
        }
        if not wins and not complete_no_error:
            failed_active = {
                **active,
                "last_returncode": returncode,
                "last_failed_at": time.time(),
            }
            return _write_progress(paths.progress, {
                **progress,
                "status": "FAILED",
                "active_batch": failed_active,
                "updated_at": time.time(),
            })
        status = "STRICT_THRESHOLD_PROVEN" if wins else "RUNNING"
        updated = dict(progress)
        updated.pop("active_batch", None)
        progress = _write_progress(paths.progress, {
            **updated,
            "status": status,
            "next_row": int(active["manifest_next_row"]),
            "batches": [*progress["batches"], batch],
            "wins": [*progress.get("wins", []), *wins],
            "updated_at": time.time(),
        })
        if status != "RUNNING":
            return progress
    return progress

def _install_control_namespace() -> Any:
    # exactification_cli is process-control only and has no scientific imports.
    from . import exactification_cli as control

    control.PROCESS_KIND = PROCESS_KIND
    control.SIDECAR_NAME = SIDECAR_NAME
    return control


def _config_from_args(args: argparse.Namespace) -> DiscoveryConfig:
    config_input = Path(args.config).expanduser()
    if config_input.is_symlink():
        raise ValueError("strict discovery config may not be a symlink")
    document = _read_json(
        config_input.resolve(strict=True),
        label="strict discovery config",
    )
    config = DiscoveryConfig.from_json(document)
    if args.cpu_list is not None:
        config = DiscoveryConfig(**{**config.as_dict(), "cpu_list": parse_cpu_list(args.cpu_list)})
    if args.nice is not None:
        config = DiscoveryConfig(**{**config.as_dict(), "nice": args.nice})
    return config.validate()


def _execute_worker(
    args: argparse.Namespace,
    paths: SidecarPaths,
    *,
    lock_fd: int | None = None,
    start_fd: int | None = None,
    isolated: bool = False,
) -> dict[str, Any]:
    control = _install_control_namespace()
    owns_lock = lock_fd is None
    if lock_fd is None:
        lock_fd = control._acquire_lock(paths.lock)
    else:
        control._validate_lock(lock_fd, paths.lock)
    if start_fd is not None:
        try:
            if os.read(start_fd, 1) != b"1":
                raise StrictDiscoveryError("parent launch barrier failed")
        finally:
            os.close(start_fd)

    stop_event = threading.Event()

    def request_stop(_signum: int, _frame: Any) -> None:
        stop_event.set()

    previous_term = signal.signal(signal.SIGTERM, request_stop)
    previous_hup = signal.signal(signal.SIGHUP, signal.SIG_IGN) if isolated else None
    lease = None
    heartbeat = None
    identity: Mapping[str, Any] | None = None
    try:
        config = _config_from_args(args)
        _native_thread_limits()
        capacity_affinity, selected = _select_cpus(config)
        identity = control._proc_identity(os.getpid())
        if identity is None:
            raise StrictDiscoveryError("cannot establish strict worker identity")
        config_path = Path(args.config).expanduser().resolve(strict=True)
        portfolio, source_path, portfolio_source = load_portfolio_manifest(
            args.portfolio_manifest,
            paths=paths,
            ranked_input=args.ranked_input,
        )
        portfolio_path = Path(
            portfolio_source["portfolio_manifest_path"]
        )
        starting = control.read_process_record(paths.process) if isolated else None
        config_sha256 = _file_sha256(config_path)
        ranked_input_sha256 = portfolio_source["ranked_input"]["sha256"]
        portfolio_manifest_sha256 = portfolio_source[
            "portfolio_manifest_file_sha256"
        ]
        if isolated and (
            not isinstance(starting, Mapping)
            or starting.get("pid") != identity.get("pid")
            or starting.get("proc_starttime") != identity.get("proc_starttime")
            or starting.get("config_sha256") != config_sha256
            or starting.get("ranked_input_sha256") != ranked_input_sha256
            or starting.get("portfolio_manifest_sha256")
            != portfolio_manifest_sha256
            or starting.get("cli_source_sha256") != _CLI_SOURCE_SHA256
        ):
            raise StrictDiscoveryError("worker inputs differ from the launch record")
        record = {
            "schema_version": control.PROCESS_SCHEMA_VERSION,
            "kind": PROCESS_KIND,
            "run_id": args.run_id,
            "repo_dir": str(paths.repo),
            "sidecar_root": str(paths.root),
            "status": "capacity-check",
            **identity,
            "isolated_session": isolated,
            "config_path": str(config_path),
            "config_sha256": config_sha256,
            "ranked_input": str(source_path),
            "ranked_input_sha256": ranked_input_sha256,
            "portfolio_manifest": str(portfolio_path),
            "portfolio_manifest_sha256": portfolio_manifest_sha256,
            "portfolio_sha256": portfolio.get("portfolio_sha256"),
            "cli_source_sha256": _assert_cli_source_unchanged(),
            "command": list(sys.argv),
            "resources": {
                "solver_slots": config.max_total_workers,
                "reserve_foreground_cpus": config.reserve_foreground_cpus,
                "nice": config.nice,
                "cpu_list": list(selected),
                "termination_grace_s": config.termination_grace_s,
            },
            "solver_termination_grace_s": config.termination_grace_s,
            "started_at": (
                starting.get("started_at")
                if isinstance(starting, Mapping)
                else control.utc_now()
            ),
            "heartbeat_at": control.utc_now(),
            "updated_at": control.utc_now(),
        }
        control.write_process_record(paths.process, record)
        heartbeat = control._Heartbeat(paths.process, identity, 15.0)
        heartbeat.start()
        policy = control.ResourcePolicy(
            solver_slots=config.max_total_workers,
            reserve_foreground_cpus=config.reserve_foreground_cpus,
            nice=config.nice,
            cpu_list=selected,
            capacity_poll_s=config.capacity_poll_s,
            termination_grace_s=config.termination_grace_s,
        )
        while not stop_event.is_set():
            try:
                lease = control._capacity_lease(policy, capacity_affinity)
                break
            except Exception as exc:
                from evaluation.solver_budget import SolverBudgetError

                if not isinstance(exc, (control.ResourceWait, SolverBudgetError)):
                    raise
                control._update_record(
                    paths.process,
                    pid=int(identity["pid"]),
                    starttime=int(identity["proc_starttime"]),
                    status="RESOURCE_WAIT",
                    resource_wait_reason=str(exc),
                )
                stop_event.wait(config.capacity_poll_s)
        if lease is None:
            result = {"status": "cancelled"}
            control._update_record(
                paths.process,
                pid=int(identity["pid"]),
                starttime=int(identity["proc_starttime"]),
                status="cancelled",
                finished_at=control.utc_now(),
            )
            return result
        _apply_resources(config, selected)
        control._update_record(
            paths.process,
            pid=int(identity["pid"]),
            starttime=int(identity["proc_starttime"]),
            status="running",
            selected_cpus=list(selected),
        )
        result = run_discovery(
            paths=paths,
            portfolio_manifest=portfolio_path,
            ranked_input=source_path,
            config=config,
            python_executable=args.python_executable,
            stop_requested=stop_event.is_set,
        )
        terminal = "cancelled" if stop_event.is_set() else (
            "completed"
            if result.get("status") in {"STRICT_THRESHOLD_PROVEN", "EXHAUSTED"}
            else str(result.get("status", "completed")).lower()
        )
        heartbeat.stop()
        heartbeat = None
        control._update_record(
            paths.process,
            pid=int(identity["pid"]),
            starttime=int(identity["proc_starttime"]),
            status=terminal,
            finished_at=control.utc_now(),
        )
        return result
    except BaseException as exc:
        if heartbeat is not None:
            heartbeat.stop()
            heartbeat = None
        if identity is not None:
            control._update_record(
                paths.process,
                pid=int(identity["pid"]),
                starttime=int(identity["proc_starttime"]),
                status="failed",
                error=f"{type(exc).__name__}: {exc}",
                finished_at=control.utc_now(),
            )
        raise
    finally:
        if heartbeat is not None:
            heartbeat.stop()
        if lease is not None:
            lease.release()
        signal.signal(signal.SIGTERM, previous_term)
        if isolated and previous_hup is not None:
            signal.signal(signal.SIGHUP, previous_hup)
        if owns_lock and lock_fd is not None:
            os.close(lock_fd)


def start_background(args: argparse.Namespace, paths: SidecarPaths) -> dict[str, Any]:
    control = _install_control_namespace()
    config = _config_from_args(args)
    config_path = Path(args.config).expanduser().resolve(strict=True)
    portfolio, source_path, portfolio_source = load_portfolio_manifest(
        args.portfolio_manifest,
        paths=paths,
        ranked_input=args.ranked_input,
    )
    portfolio_path = Path(portfolio_source["portfolio_manifest_path"])
    lock_fd = control._acquire_lock(paths.lock)
    read_fd = write_fd = log_fd = -1
    process: subprocess.Popen[Any] | None = None
    try:
        read_fd, write_fd = os.pipe()
        command = [
            str(Path(args.python_executable).expanduser()),
            "-m",
            "humanize.strict_discovery_cli",
            "_worker",
            "--repo-dir", str(paths.repo),
            "--run-id", args.run_id,
            "--portfolio-manifest", str(portfolio_path),
            "--ranked-input", str(source_path),
            "--config", str(config_path),
            "--python-executable", str(Path(args.python_executable).expanduser()),
            "--lock-fd", str(lock_fd),
            "--start-fd", str(read_fd),
        ]
        if args.cpu_list is not None:
            command.extend(["--cpu-list", args.cpu_list])
        if args.nice is not None:
            command.extend(["--nice", str(args.nice)])
        log_fd = os.open(
            paths.log,
            os.O_WRONLY | os.O_CREAT | os.O_APPEND | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        process = subprocess.Popen(
            command,
            cwd=paths.repo,
            stdin=subprocess.DEVNULL,
            stdout=log_fd,
            stderr=subprocess.STDOUT,
            close_fds=True,
            pass_fds=(lock_fd, read_fd),
            start_new_session=True,
            shell=False,
        )
        os.close(read_fd)
        read_fd = -1
        identity = None
        for _ in range(100):
            identity = control._proc_identity(process.pid)
            if identity is not None or process.poll() is not None:
                break
            time.sleep(0.01)
        if identity is None:
            raise StrictDiscoveryError("detached worker exited before identity capture")
        if identity["pgid"] != process.pid or identity["session_id"] != process.pid:
            raise StrictDiscoveryError("detached worker did not create an isolated session")
        now = control.utc_now()
        record = control.write_process_record(paths.process, {
            "schema_version": control.PROCESS_SCHEMA_VERSION,
            "kind": PROCESS_KIND,
            "run_id": args.run_id,
            "repo_dir": str(paths.repo),
            "sidecar_root": str(paths.root),
            "status": "starting",
            **identity,
            "isolated_session": True,
            "config_path": str(config_path),
            "config_sha256": _file_sha256(config_path),
            "ranked_input": str(source_path),
            "ranked_input_sha256": portfolio_source["ranked_input"]["sha256"],
            "portfolio_manifest": str(portfolio_path),
            "portfolio_manifest_sha256": portfolio_source[
                "portfolio_manifest_file_sha256"
            ],
            "portfolio_sha256": portfolio.get("portfolio_sha256"),
            "cli_source_sha256": _assert_cli_source_unchanged(),
            "command": command,
            "resources": {
                "solver_slots": config.max_total_workers,
                "reserve_foreground_cpus": config.reserve_foreground_cpus,
                "nice": config.nice,
                "cpu_list": list(config.cpu_list) if config.cpu_list else None,
                "termination_grace_s": config.termination_grace_s,
            },
            "solver_termination_grace_s": config.termination_grace_s,
            "started_at": now,
            "heartbeat_at": now,
            "updated_at": now,
        })
        os.write(write_fd, b"1")
        os.close(write_fd)
        write_fd = -1
        os.close(lock_fd)
        lock_fd = -1
        return record
    except BaseException:
        if process is not None and process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=2.0)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=2.0)
        raise
    finally:
        for descriptor in (read_fd, write_fd, log_fd, lock_fd):
            if descriptor >= 0:
                try:
                    os.close(descriptor)
                except OSError:
                    pass


def status_report(args: argparse.Namespace, paths: SidecarPaths) -> dict[str, Any]:
    control = _install_control_namespace()
    record = control.read_process_record(paths.process)
    alive, reason = (
        control.process_matches(record)
        if record is not None
        else (False, "no process record")
    )
    progress = _load_progress(paths.progress)
    return {
        "status": (
            record.get("status")
            if alive and record is not None
            else (
                progress.get("status")
                if progress is not None
                else "not-started"
            )
        ),
        "alive": alive,
        "identity_reason": reason,
        "process": record,
        "progress": progress,
        "root": str(paths.root),
    }

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    def common(command: argparse.ArgumentParser, *, worker: bool = False) -> None:
        command.add_argument(
            "--repo-dir",
            type=Path,
            default=Path(__file__).resolve().parent.parent,
        )
        command.add_argument("--run-id", required=True)
        if worker:
            command.add_argument("--portfolio-manifest", type=Path, required=True)
            command.add_argument("--ranked-input", type=Path)
            command.add_argument("--config", type=Path, required=True)
            command.add_argument("--python-executable", default=sys.executable)
            command.add_argument("--cpu-list")
            command.add_argument("--nice", type=int)

    run = subparsers.add_parser("run")
    common(run, worker=True)
    start = subparsers.add_parser("start")
    common(start, worker=True)
    status = subparsers.add_parser("status")
    common(status)
    cancel = subparsers.add_parser("cancel")
    common(cancel)
    cancel.add_argument("--grace-seconds", type=float, default=180.0)
    worker = subparsers.add_parser("_worker", help=argparse.SUPPRESS)
    common(worker, worker=True)
    worker.add_argument("--lock-fd", type=int, required=True)
    worker.add_argument("--start-fd", type=int, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = build_parser().parse_args(argv)
        create = args.command in {"run", "start", "_worker"}
        paths = sidecar_paths(args.repo_dir, args.run_id, create=create)
        if args.command == "run":
            result = _execute_worker(args, paths)
        elif args.command == "start":
            record = start_background(args, paths)
            result = {
                "status": record["status"],
                "pid": record["pid"],
                "process": str(paths.process),
                "log": str(paths.log),
            }
        elif args.command == "status":
            result = status_report(args, paths)
        elif args.command == "cancel":
            control = _install_control_namespace()
            result = control.cancel_worker(args, paths)
        elif args.command == "_worker":
            result = _execute_worker(
                args,
                paths,
                lock_fd=args.lock_fd,
                start_fd=args.start_fd,
                isolated=True,
            )
        else:
            raise AssertionError(args.command)
        print(json.dumps(result, indent=2, ensure_ascii=False, default=str), flush=True)
        return 0
    except KeyboardInterrupt:
        print(json.dumps({"status": "interrupted"}), file=sys.stderr)
        return 130
    except (OSError, RuntimeError, ValueError) as exc:
        print(
            json.dumps({"status": "error", "error": f"{type(exc).__name__}: {exc}"}),
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
