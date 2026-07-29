"""Humanize RLCR controller around OpenEvolve, MILP, and qcode artifacts."""

from __future__ import annotations

import copy
import fcntl
import hashlib
import inspect
import json
import os
import platform as platform_module
import re
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Callable, Iterator, Protocol

from .audit_state import (
    AuditOutcome,
    AuditStateError,
    authoritative_candidate_digest,
    classify_evaluation,
    is_fully_exact,
    rebuild_audit_state,
    retry_budget,
    seal_audit_attempt_evidence,
    select_retry_lane,
)
from .reviewer import CodexReviewer, build_review_prompt, validate_review
from .state import (
    EliteArchive,
    RunStore,
    atomic_write_bytes,
    atomic_write_json,
    atomic_write_jsonl,
    candidate_fom,
    code_key,
    credible_bp_candidate,
    read_jsonl_range,
    utc_now,
)


class Reviewer(Protocol):
    def review(self, prompt: str, round_dir: Path) -> dict[str, Any]: ...


MilpEvaluator = Callable[..., dict[str, Any]]
EvolutionRunner = Callable[["FlowConfig", dict[str, Any], Path], Path | None]


ROUND_TRANSACTION_PROTOCOL_VERSION = 2
ROUND_TRANSACTION_SCHEMA_VERSION = 2
LEGACY_BATCH_SCHEMA_VERSION = 1
EVOLUTION_COMPLETION_SCHEMA_VERSION = 2
EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION = 2
LOCAL_EVOLUTION_DEPENDENCIES = {
    "evaluation_evaluator": "evaluation/evaluator.py",
    "evaluation_results": "evaluation/results.py",
    "evaluation_structural_dedup": "evaluation/structural_dedup.py",
    "evaluation_bb_code": "evaluation/bb_code.py",
    "evaluation_pbb_code": "evaluation/pbb_code.py",
    "evaluation_distance": "evaluation/distance.py",
    "evaluation_distance_milp": "evaluation/distance_milp.py",
    "evaluation_tanner_equivalence": "evaluation/tanner_equivalence.py",
}
EVOLUTION_INVOCATION_FIELDS = frozenset({
    "model_names",
    "reasoning_effort",
    "codex_cli",
    "max_parallel_evaluations",
    "api_base",
    "temperature_disabled",
    "codex_version",
    "codex_cwd",
    "codex_executable_mode",
})


class RoundTransactionError(RuntimeError):
    """A round cannot be replayed without risking duplicate evolution work."""


class HumanizeRunAlreadyActiveError(RoundTransactionError):
    """Another process owns the same Humanize run identity."""


class UnresolvedAuditError(RuntimeError):
    """Stage 1 exhausted its rounds with winner-capable audits unresolved."""


@dataclass(frozen=True)
class FlowConfig:
    repo_dir: Path
    run_id: str
    max_rounds: int = 5
    iterations_per_round: int = 20
    model: str = "gpt-5.5"
    reasoning_effort: str = "xhigh"
    review_model: str = "gpt-5.5"
    review_effort: str = "xhigh"
    api_base: str | None = None
    evolution_config: Path | None = None
    evolution_seed: Path | None = None
    milp_top: int = 3
    milp_timeout_per_logical: int = 300
    milp_total_timeout: int = 7200
    milp_early_stop: int = 0
    patience: int = 3
    min_improvement: float = 0.01
    candidate_file: Path | None = None
    codex_cli: bool = False
    # Test/development-only escape hatch for evaluators that cannot emit the
    # immutable schema-v2 checkpoint contract. Production defaults fail closed.
    allow_debug_audit_evaluator: bool = False
    # Operational scheduling cap. The outer pipeline fingerprints and persists
    # it, so Humanize omits it from logical search identity to allow safe
    # checkpoint resume with a changed resource allocation.
    max_total_workers: int | None = None

    def serializable(self) -> dict[str, Any]:
        value = asdict(self)
        value["repo_dir"] = str(self.repo_dir)
        value["candidate_file"] = str(self.candidate_file) if self.candidate_file else None
        value.pop("max_total_workers", None)
        if not self.allow_debug_audit_evaluator:
            value.pop("allow_debug_audit_evaluator", None)
        # Omit unset optional launch fields so pre-fix failed runs retain an
        # identical serialized configuration and can resume their audit.
        for name in ("evolution_config", "evolution_seed"):
            path = value.get(name)
            if path is None:
                value.pop(name, None)
            else:
                value[name] = str(path)
        return value

    def validate(self) -> None:
        # RunStore.create() applies the same strict validator.  Validate here
        # as well so no evolution, candidate, or state path can be constructed
        # from an identity that would later be rewritten.
        from .pipeline_process import validate_run_id

        validate_run_id(self.run_id)
        if self.max_rounds < 1:
            raise ValueError("max_rounds must be positive")
        if self.iterations_per_round < 1 and self.candidate_file is None:
            raise ValueError("iterations_per_round must be positive")
        if self.milp_top < 0:
            raise ValueError("milp_top must be non-negative")
        if not isinstance(self.allow_debug_audit_evaluator, bool):
            raise ValueError("allow_debug_audit_evaluator must be boolean")
        if self.milp_early_stop < 0:
            raise ValueError("milp_early_stop must be non-negative")
        if self.milp_top > 0:
            for name in ("milp_timeout_per_logical", "milp_total_timeout"):
                value = getattr(self, name)
                if (
                    isinstance(value, bool)
                    or not isinstance(value, int)
                    or value < 1
                ):
                    raise ValueError(f"{name} must be a positive integer")
        if (
            self.max_total_workers is not None
            and (
                isinstance(self.max_total_workers, bool)
                or not isinstance(self.max_total_workers, int)
                or self.max_total_workers < 1
            )
        ):
            raise ValueError("max_total_workers must be a positive integer")
        if self.patience < 1:
            raise ValueError("patience must be positive")

        for name in ("evolution_config", "evolution_seed"):
            path = getattr(self, name)
            if path is not None and not path.is_file():
                raise ValueError(f"{name} does not exist: {path}")


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _file_descriptor(path: Path, label: str) -> dict[str, Any]:
    original = Path(path)
    if original.is_symlink():
        raise RoundTransactionError(f"{label} may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RoundTransactionError(f"{label} is missing: {original}") from exc
    if not resolved.is_file():
        raise RoundTransactionError(f"{label} is not a regular file: {resolved}")
    return {
        "path": str(resolved),
        "sha256": _file_sha256(resolved),
        "bytes": resolved.stat().st_size,
    }


def _tree_descriptor(path: Path, label: str) -> dict[str, Any]:
    original = Path(path)
    if original.is_symlink() or not original.is_dir():
        raise RoundTransactionError(f"{label} must be a regular directory: {original}")
    resolved = original.resolve(strict=True)
    hashes: dict[str, dict[str, Any]] = {}
    total_bytes = 0
    for item in sorted(resolved.rglob("*")):
        if item.is_symlink():
            raise RoundTransactionError(f"{label} contains a symlink: {item}")
        if item.is_dir():
            continue
        if not item.is_file():
            raise RoundTransactionError(f"{label} contains a non-file: {item}")
        relative = item.relative_to(resolved).as_posix()
        size = item.stat().st_size
        hashes[relative] = {"sha256": _file_sha256(item), "bytes": size}
        total_bytes += size
    encoded = json.dumps(hashes, sort_keys=True, separators=(",", ":")).encode()
    return {
        "path": str(resolved),
        "sha256": hashlib.sha256(encoded).hexdigest(),
        "bytes": total_bytes,
        "files": len(hashes),
    }


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _quarantined_artifact_descriptor(
    path: Path,
    label: str,
) -> dict[str, Any]:
    if path.is_symlink():
        target = os.readlink(path).encode("utf-8", errors="surrogateescape")
        return {
            "path": str(path.absolute()),
            "kind": "symlink",
            "sha256": hashlib.sha256(target).hexdigest(),
            "bytes": len(target),
        }
    if path.is_dir():
        descriptor = _tree_descriptor(path, label)
        descriptor["kind"] = "directory"
        return descriptor
    descriptor = _file_descriptor(path, label)
    descriptor["kind"] = "file"
    return descriptor


def _read_json_object(path: Path, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise RoundTransactionError(f"{label} must be a regular file: {path}")
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise RoundTransactionError(f"cannot read {label}: {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise RoundTransactionError(f"{label} must contain a JSON object: {path}")
    return value


def _checkpoint_descriptor(
    output_dir: Path,
    checkpoint: Path,
    *,
    expected_iteration: int | None = None,
) -> dict[str, Any]:
    """Validate one complete checkpoint owned by this evolution output."""
    checkpoint_root = (output_dir / "checkpoints").resolve()
    original = Path(checkpoint)
    if original.is_symlink():
        raise RoundTransactionError(f"checkpoint may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RoundTransactionError(f"checkpoint is missing: {original}") from exc
    if not resolved.is_dir() or resolved.parent != checkpoint_root:
        raise RoundTransactionError(
            f"checkpoint does not belong to this run: {resolved}"
        )
    prefix = "checkpoint_"
    if not resolved.name.startswith(prefix):
        raise RoundTransactionError(f"invalid checkpoint directory name: {resolved}")
    try:
        named_iteration = int(resolved.name[len(prefix):])
    except ValueError as exc:
        raise RoundTransactionError(
            f"invalid checkpoint iteration in path: {resolved}"
        ) from exc

    metadata_path = resolved / "metadata.json"
    best_path = resolved / "best_program.py"
    best_info_path = resolved / "best_program_info.json"
    programs_dir = resolved / "programs"
    metadata = _read_json_object(metadata_path, "checkpoint metadata")
    best_info = _read_json_object(best_info_path, "checkpoint best-program info")
    if best_path.is_symlink() or not best_path.is_file() or best_path.stat().st_size < 1:
        raise RoundTransactionError(
            f"checkpoint best_program.py is missing or empty: {best_path}"
        )
    if programs_dir.is_symlink() or not programs_dir.is_dir():
        raise RoundTransactionError(
            f"checkpoint programs directory is missing: {programs_dir}"
        )

    iteration = metadata.get("last_iteration")
    if isinstance(iteration, bool) or not isinstance(iteration, int) or iteration < 0:
        raise RoundTransactionError(
            f"checkpoint last_iteration is invalid: {metadata_path}: {iteration!r}"
        )
    if iteration != named_iteration:
        raise RoundTransactionError(
            f"checkpoint path/metadata iteration mismatch: {named_iteration} != {iteration}"
        )
    if expected_iteration is not None and iteration != expected_iteration:
        raise RoundTransactionError(
            f"checkpoint iteration mismatch: expected {expected_iteration}, got {iteration}"
        )

    archive = metadata.get("archive")
    best_id = metadata.get("best_program_id")
    if (
        not isinstance(archive, list)
        or not archive
        or any(not isinstance(item, str) or not item for item in archive)
        or not isinstance(best_id, str)
        or not best_id
    ):
        raise RoundTransactionError(
            f"checkpoint archive/best_program_id is incomplete: {metadata_path}"
        )
    if best_info.get("id") != best_id or best_info.get("current_iteration") != iteration:
        raise RoundTransactionError(
            f"checkpoint best-program info disagrees with metadata: {best_info_path}"
        )

    referenced = set(archive)
    referenced.add(best_id)

    def add_optional_reference(value: Any, label: str) -> None:
        if value in (None, ""):
            return
        if not isinstance(value, str):
            raise RoundTransactionError(
                f"checkpoint {label} contains a non-string program id"
            )
        referenced.add(value)

    islands = metadata.get("islands", [])
    if not isinstance(islands, list) or any(
        not isinstance(island, list) for island in islands
    ):
        raise RoundTransactionError("checkpoint islands metadata is invalid")
    for island in islands:
        for program_id in island:
            add_optional_reference(program_id, "islands")
    island_best = metadata.get("island_best_programs", [])
    if not isinstance(island_best, list):
        raise RoundTransactionError(
            "checkpoint island_best_programs metadata is invalid"
        )
    for program_id in island_best:
        add_optional_reference(program_id, "island_best_programs")
    feature_maps = metadata.get("island_feature_maps", [])
    if not isinstance(feature_maps, list) or any(
        not isinstance(feature_map, dict) for feature_map in feature_maps
    ):
        raise RoundTransactionError(
            "checkpoint island_feature_maps metadata is invalid"
        )
    for feature_map in feature_maps:
        for program_id in feature_map.values():
            add_optional_reference(program_id, "island_feature_maps")

    program_files = sorted(programs_dir.glob("*.json"))
    if not program_files:
        raise RoundTransactionError(f"checkpoint contains no programs: {programs_dir}")
    program_ids: set[str] = set()
    best_program_code: str | None = None
    file_hashes: dict[str, str] = {
        "metadata.json": _file_sha256(metadata_path),
        "best_program.py": _file_sha256(best_path),
        "best_program_info.json": _file_sha256(best_info_path),
    }
    for program_path in program_files:
        program = _read_json_object(program_path, "checkpoint program")
        program_id = program.get("id")
        if program_id != program_path.stem:
            raise RoundTransactionError(
                f"checkpoint program id/path mismatch: {program_path}"
            )
        code = program.get("code")
        metrics = program.get("metrics")
        if not isinstance(code, str) or not code:
            raise RoundTransactionError(
                f"checkpoint program has no non-empty code: {program_path}"
            )
        if not isinstance(metrics, dict):
            raise RoundTransactionError(
                f"checkpoint program metrics is not an object: {program_path}"
            )
        program_ids.add(program_id)
        if program_id == best_id:
            best_program_code = code
        file_hashes[f"programs/{program_path.name}"] = _file_sha256(program_path)
    missing = sorted(referenced - program_ids)
    if missing:
        raise RoundTransactionError(
            "checkpoint is missing referenced programs: " + ", ".join(missing)
        )
    if best_program_code is None or best_path.read_text() != best_program_code:
        raise RoundTransactionError(
            "checkpoint best_program.py does not match the stored best program code"
        )
    checkpoint_hash = hashlib.sha256(
        json.dumps(file_hashes, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return {
        "path": str(resolved),
        "last_iteration": iteration,
        "sha256": checkpoint_hash,
        "programs": len(program_files),
    }


def _assert_checkpoint_frontier(
    output_dir: Path,
    base_iteration: int,
    *,
    allowed_iterations: frozenset[int] = frozenset(),
) -> None:
    """Reject checkpoint directories not bound to the durable slice frontier."""
    checkpoint_root = output_dir / "checkpoints"
    if checkpoint_root.is_symlink():
        raise RoundTransactionError(
            f"checkpoint root may not be a symlink: {checkpoint_root}"
        )
    if not checkpoint_root.exists():
        return
    if not checkpoint_root.is_dir():
        raise RoundTransactionError(
            f"checkpoint root is not a directory: {checkpoint_root}"
        )
    for checkpoint in checkpoint_root.iterdir():
        if not checkpoint.name.startswith("checkpoint_"):
            continue
        suffix = checkpoint.name[len("checkpoint_"):]
        try:
            iteration = int(suffix)
        except ValueError as exc:
            raise RoundTransactionError(
                f"checkpoint frontier contains an invalid entry: {checkpoint}"
            ) from exc
        if checkpoint.name != f"checkpoint_{iteration}":
            raise RoundTransactionError(
                f"checkpoint frontier contains a non-canonical entry: {checkpoint}"
            )
        if iteration <= base_iteration:
            continue
        if checkpoint.is_symlink():
            raise RoundTransactionError(
                f"checkpoint frontier contains a symlink: {checkpoint}"
            )
        if iteration not in allowed_iterations:
            raise RoundTransactionError(
                "checkpoint frontier contains an unbound checkpoint newer than "
                f"the durable base: {checkpoint}"
            )


def _completion_marker_path(round_dir: Path) -> Path:
    return round_dir / "openevolve-completed.json"


def _slice_witness_path(round_dir: Path) -> Path:
    return round_dir / "openevolve-slice-witness.json"


def _round_lifecycle_lock_path(round_dir: Path) -> Path:
    return round_dir / "openevolve-lifecycle.lock"


@dataclass(frozen=True)
class _HumanizeRunLease:
    fd: int
    path: Path
    owner_pid: int
    token: object


_HUMANIZE_RUN_LEASE_REGISTRY_LOCK = threading.RLock()
_ACTIVE_HUMANIZE_RUN_LEASES: dict[object, _HumanizeRunLease] = {}


def _validate_humanize_run_lease_inode(
    root_fd: int,
    root_path: Path,
    lock_fd: int,
    lock_name: str,
) -> None:
    """Bind an acquired descriptor to one regular file in the fixed run root."""
    try:
        descriptor_root = os.fstat(root_fd)
        path_root = os.stat(root_path, follow_symlinks=False)
        descriptor_lock = os.fstat(lock_fd)
        path_lock = os.stat(
            lock_name,
            dir_fd=root_fd,
            follow_symlinks=False,
        )
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot validate Humanize run lease: {root_path / lock_name}: {exc}"
        ) from exc
    if (
        not stat.S_ISDIR(descriptor_root.st_mode)
        or not stat.S_ISDIR(path_root.st_mode)
        or (descriptor_root.st_dev, descriptor_root.st_ino)
        != (path_root.st_dev, path_root.st_ino)
    ):
        raise RoundTransactionError(
            f"Humanize run root was replaced or is unsafe: {root_path}"
        )
    if (
        not stat.S_ISREG(descriptor_lock.st_mode)
        or not stat.S_ISREG(path_lock.st_mode)
    ):
        raise RoundTransactionError(
            "Humanize run lease must be a regular file: "
            f"{root_path / lock_name}"
        )
    if (descriptor_lock.st_dev, descriptor_lock.st_ino) != (
        path_lock.st_dev,
        path_lock.st_ino,
    ):
        raise RoundTransactionError(
            f"Humanize run lease path was replaced: {root_path / lock_name}"
        )


def _validate_inherited_humanize_run_lease(
    store: RunStore,
    lease: _HumanizeRunLease,
) -> None:
    """Accept only the exact active in-process lease for this run."""
    if not isinstance(lease, _HumanizeRunLease):
        raise RoundTransactionError("inherited Humanize run lease has invalid type")
    expected_path = store.lock_path.absolute()
    if lease.path != expected_path or lease.owner_pid != os.getpid():
        raise RoundTransactionError(
            "inherited Humanize run lease belongs to a different run or process"
        )
    with _HUMANIZE_RUN_LEASE_REGISTRY_LOCK:
        if _ACTIVE_HUMANIZE_RUN_LEASES.get(lease.token) is not lease:
            raise RoundTransactionError(
                "inherited Humanize run lease is not currently active"
            )

    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RoundTransactionError("O_NOFOLLOW is required for Humanize run leases")
    root_path = store.root.absolute()
    root_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0)
        | nofollow
    )
    try:
        root_fd = os.open(root_path, root_flags)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot validate inherited Humanize run root: {root_path}: {exc}"
        ) from exc
    try:
        _validate_humanize_run_lease_inode(
            root_fd,
            root_path,
            lease.fd,
            expected_path.name,
        )
    finally:
        os.close(root_fd)


@contextmanager
def _acquire_humanize_run_lease(
    store: RunStore,
) -> Iterator[_HumanizeRunLease]:
    """Exclusively own one direct Humanize run for its complete execution."""
    root_path = store.root.absolute()
    lock_path = store.lock_path.absolute()
    if lock_path.parent != root_path or lock_path.name != "run.lock":
        raise RoundTransactionError(
            f"Humanize run lease path is outside its fixed run root: {lock_path}"
        )
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RoundTransactionError("O_NOFOLLOW is required for Humanize run leases")

    root_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0)
        | nofollow
    )
    try:
        root_fd = os.open(root_path, root_flags)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot open Humanize run root for its lease: {root_path}: {exc}"
        ) from exc

    lock_fd: int | None = None
    locked = False
    try:
        lock_flags = (
            os.O_RDWR
            | os.O_CREAT
            | getattr(os, "O_CLOEXEC", 0)
            | getattr(os, "O_NONBLOCK", 0)
            | nofollow
        )
        try:
            lock_fd = os.open(
                lock_path.name,
                lock_flags,
                0o600,
                dir_fd=root_fd,
            )
        except OSError as exc:
            raise RoundTransactionError(
                f"cannot open Humanize run lease: {lock_path}: {exc}"
            ) from exc
        _validate_humanize_run_lease_inode(
            root_fd,
            root_path,
            lock_fd,
            lock_path.name,
        )
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise HumanizeRunAlreadyActiveError(
                f"Humanize run {store.run_id!r} is already active"
            ) from exc
        locked = True
        _validate_humanize_run_lease_inode(
            root_fd,
            root_path,
            lock_fd,
            lock_path.name,
        )
        lease = _HumanizeRunLease(
            fd=lock_fd,
            path=lock_path,
            owner_pid=os.getpid(),
            token=object(),
        )
        with _HUMANIZE_RUN_LEASE_REGISTRY_LOCK:
            _ACTIVE_HUMANIZE_RUN_LEASES[lease.token] = lease
        try:
            yield lease
        finally:
            with _HUMANIZE_RUN_LEASE_REGISTRY_LOCK:
                if _ACTIVE_HUMANIZE_RUN_LEASES.get(lease.token) is lease:
                    del _ACTIVE_HUMANIZE_RUN_LEASES[lease.token]
    finally:
        if lock_fd is not None:
            try:
                if locked:
                    fcntl.flock(lock_fd, fcntl.LOCK_UN)
            finally:
                os.close(lock_fd)
        os.close(root_fd)


@dataclass(frozen=True)
class _RoundLifecycleLease:
    fd: int
    path: Path


def _validate_round_lifecycle_inode(fd: int, path: Path) -> None:
    try:
        descriptor_stat = os.fstat(fd)
        path_stat = os.stat(path, follow_symlinks=False)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot validate OpenEvolve lifecycle lease: {path}: {exc}"
        ) from exc
    if not stat.S_ISREG(descriptor_stat.st_mode) or not stat.S_ISREG(
        path_stat.st_mode
    ):
        raise RoundTransactionError(
            f"OpenEvolve lifecycle lease must be a regular file: {path}"
        )
    if (descriptor_stat.st_dev, descriptor_stat.st_ino) != (
        path_stat.st_dev,
        path_stat.st_ino,
    ):
        raise RoundTransactionError(
            f"OpenEvolve lifecycle lease path was replaced: {path}"
        )


@contextmanager
def _acquire_round_lifecycle_lease(
    round_dir: Path,
) -> Iterator[_RoundLifecycleLease]:
    """Hold one fixed round lease across recovery and the whole child tree."""
    original_round = round_dir.absolute()
    try:
        resolved_round = round_dir.resolve(strict=True)
    except OSError as exc:
        raise RoundTransactionError(
            f"round directory is missing for lifecycle lease: {round_dir}"
        ) from exc
    if resolved_round != original_round or not resolved_round.is_dir():
        raise RoundTransactionError(
            f"round directory must be canonical and may not use symlinks: {round_dir}"
        )
    path = _round_lifecycle_lock_path(original_round).absolute()
    if path.is_symlink():
        raise RoundTransactionError(
            f"OpenEvolve lifecycle lease may not be a symlink: {path}"
        )
    flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_CLOEXEC", 0)
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RoundTransactionError("O_NOFOLLOW is required for lifecycle leases")
    flags |= nofollow
    try:
        fd = os.open(path, flags, 0o600)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot open OpenEvolve lifecycle lease: {path}: {exc}"
        ) from exc
    try:
        _validate_round_lifecycle_inode(fd, path)
        fcntl.flock(fd, fcntl.LOCK_EX)
        _validate_round_lifecycle_inode(fd, path)
        yield _RoundLifecycleLease(fd=fd, path=path)
    finally:
        try:
            fcntl.flock(fd, fcntl.LOCK_UN)
        finally:
            os.close(fd)


def _process_group_exists(process_group: int) -> bool:
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _terminate_process_group(
    process: subprocess.Popen,
    *,
    grace_seconds: float = 2.0,
) -> None:
    """Terminate the launcher and every process left in its private group."""
    process_group = process.pid
    try:
        os.killpg(process_group, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process_group, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()

    deadline = time.monotonic() + grace_seconds
    while _process_group_exists(process_group) and time.monotonic() < deadline:
        time.sleep(0.05)
    if _process_group_exists(process_group):
        try:
            os.killpg(process_group, signal.SIGKILL)
        except ProcessLookupError:
            pass


def _wait_for_managed_process(
    process: subprocess.Popen,
    command: list[str],
) -> None:
    try:
        return_code = process.wait()
        _terminate_process_group(process)
    except BaseException:
        # A first SIGTERM can arrive during normal post-wait cleanup.  The
        # pipeline handler masks subsequent SIGTERM before raising, so retry
        # the cleanup here to avoid abandoning surviving group members.
        _terminate_process_group(process)
        raise
    if return_code:
        raise subprocess.CalledProcessError(return_code, command)


def _expected_evolution_config(config: FlowConfig) -> Path:
    return Path(os.path.abspath(
        config.evolution_config
        or config.repo_dir / "evolve" / "config.yaml"
    ))


def _expected_evolution_seed(config: FlowConfig) -> Path:
    return Path(os.path.abspath(
        config.evolution_seed
        or config.repo_dir / "evolve" / "seed_solution.py"
    ))


def _expected_evolution_launcher(config: FlowConfig) -> Path:
    return Path(os.path.abspath(config.repo_dir / "evolve" / "run_evolution.py"))


def _expected_evolution_evaluator(config: FlowConfig) -> Path:
    return Path(
        os.path.abspath(config.repo_dir / "evolve" / "openevolve_evaluator.py")
    )


def _expected_evolution_backend(config: FlowConfig) -> Path:
    return Path(os.path.abspath(config.repo_dir / "evolve" / "codex_cli_llm.py"))


def _configured_evolution_workers(config_path: Path) -> int:
    try:
        lines = config_path.read_text().splitlines()
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot read evolution config worker budget: {config_path}: {exc}"
        ) from exc
    evaluator_indent: int | None = None
    configured_values: list[int] = []
    for raw_line in lines:
        content = raw_line.split("#", 1)[0].rstrip()
        if not content:
            continue
        indent = len(content) - len(content.lstrip())
        stripped = content.strip()
        if evaluator_indent is None:
            if stripped == "evaluator:":
                evaluator_indent = indent
            continue
        if indent <= evaluator_indent:
            evaluator_indent = None
            if stripped == "evaluator:":
                evaluator_indent = indent
            continue
        matched = re.fullmatch(
            r"parallel_evaluations:\s*(?:[\"']([0-9]+)[\"']|([0-9]+))",
            stripped,
        )
        if matched:
            configured_values.append(
                int(matched.group(1) or matched.group(2))
            )
    configured = (
        configured_values[0] if len(configured_values) == 1 else None
    )
    if (
        isinstance(configured, bool)
        or not isinstance(configured, int)
        or configured < 1
    ):
        raise RoundTransactionError(
            "evolution config evaluator.parallel_evaluations must be "
            "a positive integer"
        )
    return configured


def _resolve_native_codex_path(requested_bin: str) -> Path:
    launcher = shutil.which(requested_bin)
    if launcher is None:
        raise RoundTransactionError(
            f"Codex CLI executable is unavailable: {requested_bin}"
        )
    launcher_path = Path(launcher).resolve(strict=True)
    with launcher_path.open("rb") as stream:
        magic = stream.read(4)
    if magic in (b"\x7fELF", b"MZ\x90\x00"):
        return launcher_path
    if launcher_path.name != "codex.js" or launcher_path.parent.name != "bin":
        raise RoundTransactionError(
            "managed QCODE_CODEX_BIN must be the official codex.js launcher "
            "or a native Codex executable"
        )
    target = {
        ("linux", "x86_64"): (
            "@openai/codex-linux-x64",
            "x86_64-unknown-linux-musl",
            "codex",
        ),
        ("linux", "aarch64"): (
            "@openai/codex-linux-arm64",
            "aarch64-unknown-linux-musl",
            "codex",
        ),
        ("darwin", "x86_64"): (
            "@openai/codex-darwin-x64",
            "x86_64-apple-darwin",
            "codex",
        ),
        ("darwin", "arm64"): (
            "@openai/codex-darwin-arm64",
            "aarch64-apple-darwin",
            "codex",
        ),
        ("windows", "amd64"): (
            "@openai/codex-win32-x64",
            "x86_64-pc-windows-msvc",
            "codex.exe",
        ),
        ("windows", "arm64"): (
            "@openai/codex-win32-arm64",
            "aarch64-pc-windows-msvc",
            "codex.exe",
        ),
    }.get(
        (
            platform_module.system().lower(),
            platform_module.machine().lower(),
        )
    )
    if target is None:
        raise RoundTransactionError(
            "unsupported managed Codex platform: "
            f"{platform_module.system().lower()}/"
            f"{platform_module.machine().lower()}"
        )
    package_name, target_triple, executable_name = target
    package_root = launcher_path.parent.parent
    for candidate in (
        package_root
        / "node_modules"
        / Path(*package_name.split("/"))
        / "vendor"
        / target_triple
        / "bin"
        / executable_name,
        package_root / "vendor" / target_triple / "bin" / executable_name,
    ):
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            continue
        if resolved.is_file():
            return resolved
    raise RoundTransactionError(
        "cannot resolve the official Codex launcher to its native executable"
    )


def _codex_version(executable: Path) -> str:
    try:
        completed = subprocess.run(
            [str(executable), "--version"],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise RoundTransactionError(
            "cannot identify the Codex CLI version"
        ) from exc
    version = completed.stdout.strip()
    if not version or len(version) > 500:
        raise RoundTransactionError(
            "Codex CLI returned an invalid version identity"
        )
    return version


def _fresh_codex_binding(
    config: FlowConfig,
) -> tuple[dict[str, Any], str, str]:
    executable = _resolve_native_codex_path(
        os.environ.get("QCODE_CODEX_BIN", "codex")
    )
    if not executable.is_file() or not os.access(executable, os.X_OK):
        raise RoundTransactionError(
            f"Codex CLI native binary is not executable: {executable}"
        )
    identity = _file_descriptor(
        executable, "Codex CLI native executable"
    )
    identity["mode"] = stat.S_IMODE(executable.stat().st_mode)
    cwd = str(config.repo_dir.resolve(strict=True))
    return identity, _codex_version(executable), cwd


def _resolved_api_base(config: FlowConfig) -> str:
    if config.api_base:
        return config.api_base
    for name in ("OPENAI_API_BASE", "LITELLM_API_BASE"):
        value = os.environ.get(name)
        if value:
            return value
    return "http://localhost:4000/v1"


def _fresh_invocation_binding(
    config: FlowConfig,
    *,
    codex_identity: dict[str, Any] | None,
    codex_version: str | None,
    codex_cwd: str | None,
) -> dict[str, Any]:
    configured_workers = _configured_evolution_workers(
        _expected_evolution_config(config)
    )
    worker_cap = config.max_total_workers
    effective_workers = (
        configured_workers
        if worker_cap is None
        else min(configured_workers, worker_cap)
    )
    return {
        "model_names": [config.model],
        "reasoning_effort": config.reasoning_effort,
        "codex_cli": config.codex_cli,
        "max_parallel_evaluations": effective_workers,
        "api_base": _resolved_api_base(config),
        "temperature_disabled": True,
        "codex_version": codex_version,
        "codex_cwd": codex_cwd,
        "codex_executable_mode": (
            None if codex_identity is None else codex_identity["mode"]
        ),
    }


def _evolution_launch_binding(
    config: FlowConfig,
    *,
    context_path: Path,
    codex_executable: dict[str, Any] | None = None,
) -> dict[str, dict[str, Any]]:
    binding = {
        "config": _file_descriptor(
            _expected_evolution_config(config), "evolution config"
        ),
        "seed": _file_descriptor(
            _expected_evolution_seed(config), "evolution seed"
        ),
        "launcher": _file_descriptor(
            _expected_evolution_launcher(config), "evolution launcher"
        ),
        "evaluator": _file_descriptor(
            _expected_evolution_evaluator(config), "evolution evaluator"
        ),
        "context": _file_descriptor(
            context_path, "evolution humanize context"
        ),
    }
    for name, relative_path in LOCAL_EVOLUTION_DEPENDENCIES.items():
        binding[name] = _file_descriptor(
            config.repo_dir / relative_path,
            f"evolution evaluator dependency {name}",
        )
    if config.codex_cli:
        if codex_executable is None:
            raise RoundTransactionError(
                "Codex evolution launch has no frozen executable identity"
            )
        binding["backend"] = _file_descriptor(
            _expected_evolution_backend(config), "evolution model backend"
        )
        observed = _file_descriptor(
            Path(str(codex_executable.get("path", ""))),
            "Codex CLI native executable",
        )
        observed["mode"] = stat.S_IMODE(Path(observed["path"]).stat().st_mode)
        if observed != codex_executable:
            raise RoundTransactionError(
                "Codex CLI native executable changed after transaction prepare"
            )
        binding["codex_executable"] = dict(codex_executable)
    return binding


def _validate_invocation_binding(
    config: FlowConfig,
    invocation: Any,
    launch_binding: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    if not isinstance(invocation, dict) or set(invocation) != set(
        EVOLUTION_INVOCATION_FIELDS
    ):
        raise RoundTransactionError(
            "evolution invocation binding fields are incomplete"
        )
    if invocation["model_names"] != [config.model]:
        raise RoundTransactionError("evolution model binding changed")
    if invocation["reasoning_effort"] != config.reasoning_effort:
        raise RoundTransactionError("evolution reasoning binding changed")
    if invocation["codex_cli"] is not config.codex_cli:
        raise RoundTransactionError("evolution backend selection changed")
    workers = invocation["max_parallel_evaluations"]
    configured_workers = _configured_evolution_workers(
        Path(launch_binding["config"]["path"])
    )
    expected_workers = (
        configured_workers
        if config.max_total_workers is None
        else min(configured_workers, config.max_total_workers)
    )
    if (
        isinstance(workers, bool)
        or not isinstance(workers, int)
        or workers != expected_workers
    ):
        raise RoundTransactionError(
            "evolution worker binding does not match the unified worker budget"
        )
    api_base = invocation["api_base"]
    if not isinstance(api_base, str) or not api_base:
        raise RoundTransactionError("evolution API base binding is invalid")
    if config.api_base is not None and api_base != config.api_base:
        raise RoundTransactionError("evolution API base binding changed")
    if invocation["temperature_disabled"] is not True:
        raise RoundTransactionError(
            "managed evolution must freeze temperature-disabled mode"
        )

    codex_fields = (
        invocation["codex_version"],
        invocation["codex_cwd"],
        invocation["codex_executable_mode"],
    )
    if config.codex_cli:
        if set(("backend", "codex_executable")) - set(launch_binding):
            raise RoundTransactionError("Codex launch binding is incomplete")
        executable = launch_binding["codex_executable"]
        path = Path(str(executable.get("path", "")))
        observed = _file_descriptor(path, "Codex CLI native executable")
        observed["mode"] = stat.S_IMODE(path.stat().st_mode)
        if observed != executable:
            raise RoundTransactionError(
                "Codex CLI native executable changed after transaction prepare"
            )
        if (
            invocation["codex_executable_mode"] != executable["mode"]
            or invocation["codex_cwd"]
            != str(config.repo_dir.resolve(strict=True))
            or not isinstance(invocation["codex_version"], str)
            or not invocation["codex_version"]
            or _codex_version(path) != invocation["codex_version"]
        ):
            raise RoundTransactionError(
                "Codex execution identity changed after transaction prepare"
            )
    elif any(value is not None for value in codex_fields):
        raise RoundTransactionError(
            "non-Codex invocation contains Codex execution fields"
        )
    return dict(invocation)


def _freeze_round_context(
    config: FlowConfig,
    state: dict[str, Any],
    round_dir: Path,
) -> Path:
    context_path = Path(os.path.abspath(round_dir / "search-context.md"))
    if context_path.is_symlink() or context_path.exists():
        raise RoundTransactionError(
            f"refusing to overwrite an unbound evolution context: {context_path}"
        )
    memory_path = (
        config.repo_dir
        / "results"
        / "humanize"
        / config.run_id
        / "bitlesson.md"
    )
    context_parts = [memory_path.read_text()] if memory_path.is_file() else []
    previous_number = state.get("current_round")
    if (
        not isinstance(previous_number, bool)
        and isinstance(previous_number, int)
        and previous_number > 0
    ):
        previous_review = (
            round_dir.parent
            / f"round-{previous_number:03d}"
            / "review.json"
        )
        if previous_review.is_file():
            review = _read_json_object(previous_review, "previous review")
            focus = review.get("recommended_focus", [])
            if focus:
                if not isinstance(focus, list):
                    raise RoundTransactionError(
                        "previous reviewer focus must be a list"
                    )
                context_parts.append(
                    "Previous independent reviewer focus:\n- "
                    + "\n- ".join(map(str, focus))
                )
    payload = ("\n\n".join(context_parts) + "\n").encode("utf-8")
    identity = atomic_write_bytes(context_path, payload)
    observed = _file_descriptor(context_path, "evolution humanize context")
    if (
        observed["sha256"] != identity["sha256"]
        or observed["bytes"] != identity["bytes"]
    ):
        raise RoundTransactionError(
            "frozen evolution context identity is inconsistent"
        )
    return context_path


def _quarantine_orphan_round_context(round_dir: Path) -> Path | None:
    """Preserve a context left by a crash before manifest publication."""
    context_path = Path(os.path.abspath(round_dir / "search-context.md"))
    if not context_path.exists() and not context_path.is_symlink():
        return None
    if context_path.is_symlink() or not context_path.is_file():
        raise RoundTransactionError(
            f"orphan evolution context is not a regular file: {context_path}"
        )
    payload = context_path.read_bytes()
    digest = hashlib.sha256(payload).hexdigest()
    index = 1
    while True:
        destination = round_dir / (
            f"orphan-search-context-{digest[:16]}-{index:03d}.md"
        )
        if not destination.exists() and not destination.is_symlink():
            break
        index += 1
    context_path.replace(destination)
    _fsync_directory(round_dir)
    descriptor = _file_descriptor(
        destination, "orphan evolution context archive"
    )
    if (
        descriptor["sha256"] != digest
        or descriptor["bytes"] != len(payload)
    ):
        raise RoundTransactionError(
            "orphan evolution context archive changed during quarantine"
        )
    return destination


def _fresh_evolution_bindings(
    config: FlowConfig,
    state: dict[str, Any],
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    context_path = _freeze_round_context(config, state, round_dir)
    codex_identity: dict[str, Any] | None = None
    version: str | None = None
    cwd: str | None = None
    if config.codex_cli:
        codex_identity, version, cwd = _fresh_codex_binding(config)
    launch = _evolution_launch_binding(
        config,
        context_path=context_path,
        codex_executable=codex_identity,
    )
    invocation = _fresh_invocation_binding(
        config,
        codex_identity=codex_identity,
        codex_version=version,
        codex_cwd=cwd,
    )
    _validate_invocation_binding(config, invocation, launch)
    return launch, invocation


def _slice_iterations_sha256(start_iteration: int, count: int) -> str:
    iterations = list(range(start_iteration, start_iteration + count))
    encoded = json.dumps(iterations, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validate_slice_witness(
    witness_path: Path,
    config: FlowConfig,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    launch_binding: dict[str, dict[str, Any]],
    invocation_binding: dict[str, Any],
) -> dict[str, Any]:
    witness = _read_json_object(witness_path, "OpenEvolve slice witness")
    binding = launch_binding
    invocation = _validate_invocation_binding(
        config, invocation_binding, binding
    )
    base_iteration = (
        0 if base_checkpoint is None else int(base_checkpoint["last_iteration"])
    )
    start_iteration = base_iteration + 1
    count = config.iterations_per_round
    end_iteration = base_iteration + count
    expected: dict[str, Any] = {
        "schema_version": EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
        "status": "completed",
        "output_dir": str(
            (
                config.repo_dir
                / "results"
                / "evolution"
                / f"humanize_{config.run_id}"
            ).resolve()
        ),
        "resume_checkpoint": (
            None if base_checkpoint is None else base_checkpoint["path"]
        ),
        "base_last_iteration": base_iteration,
        "iterations_requested": count,
        "slice_start_iteration": start_iteration,
        "slice_end_iteration": end_iteration,
        "slice_iteration_count": count,
        "slice_iterations_sha256": _slice_iterations_sha256(
            start_iteration, count
        ),
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
    }
    for name, descriptor in binding.items():
        for field in ("path", "sha256", "bytes"):
            expected[f"{name}_{field}"] = descriptor[field]
    expected.update(invocation)
    for key, value in expected.items():
        if witness.get(key) != value:
            raise RoundTransactionError(
                f"OpenEvolve slice witness mismatch for {key}: "
                f"expected {value!r}, got {witness.get(key)!r}"
            )

    expected_iterations = list(range(start_iteration, end_iteration + 1))
    attempts = witness.get("submission_attempts")
    if not isinstance(attempts, list) or len(attempts) != count:
        raise RoundTransactionError(
            "OpenEvolve slice witness has incomplete submission attempts"
        )
    if [attempt.get("iteration") for attempt in attempts if isinstance(attempt, dict)] != expected_iterations:
        raise RoundTransactionError(
            "OpenEvolve slice witness submission iterations are not exact"
        )
    for attempt in attempts:
        if (
            not isinstance(attempt, dict)
            or isinstance(attempt.get("island_id"), bool)
            or not isinstance(attempt.get("island_id"), int)
            or attempt.get("result") != "future"
        ):
            raise RoundTransactionError(
                "OpenEvolve slice witness contains an invalid submission"
            )

    outcomes = witness.get("outcomes")
    if not isinstance(outcomes, list) or len(outcomes) != count:
        raise RoundTransactionError(
            "OpenEvolve slice witness has incomplete future outcomes"
        )
    if [outcome.get("iteration") for outcome in outcomes if isinstance(outcome, dict)] != expected_iterations:
        raise RoundTransactionError(
            "OpenEvolve slice witness outcome iterations are not exact"
        )
    successful = 0
    worker_errors = 0
    witnessed_program_ids: set[str] = set()
    for outcome in outcomes:
        if not isinstance(outcome, dict):
            raise RoundTransactionError(
                "OpenEvolve slice witness outcome is not an object"
            )
        iteration = int(outcome["iteration"])
        status = outcome.get("status")
        if status == "worker_error":
            worker_errors += 1
            digest = outcome.get("error_sha256")
            size = outcome.get("error_bytes")
            if (
                not isinstance(digest, str)
                or len(digest) != 64
                or any(
                    character not in "0123456789abcdef"
                    for character in digest
                )
                or isinstance(size, bool)
                or not isinstance(size, int)
                or size < 1
            ):
                raise RoundTransactionError(
                    "OpenEvolve slice witness worker error identity is invalid"
                )
        elif status == "program_added":
            successful += 1
            program_id = outcome.get("program_id")
            program_sha256 = outcome.get("program_sha256")
            program_bytes = outcome.get("program_bytes")
            if (
                not isinstance(program_id, str)
                or not program_id
                or program_id in witnessed_program_ids
                or not isinstance(program_sha256, str)
                or len(program_sha256) != 64
                or any(
                    character not in "0123456789abcdef"
                    for character in program_sha256
                )
                or isinstance(program_bytes, bool)
                or not isinstance(program_bytes, int)
                or program_bytes < 1
            ):
                raise RoundTransactionError(
                    "OpenEvolve slice witness program identity is invalid"
                )
            witnessed_program_ids.add(program_id)
        else:
            raise RoundTransactionError(
                f"OpenEvolve slice witness has invalid outcome status: {status!r}"
            )
    if successful < 1:
        raise RoundTransactionError(
            "OpenEvolve slice witness has no successful program"
        )
    if (
        witness.get("successful_evaluations") != successful
        or witness.get("worker_errors") != worker_errors
        or successful + worker_errors != count
    ):
        raise RoundTransactionError(
            "OpenEvolve slice witness outcome counts are inconsistent"
        )

    saves = witness.get("checkpoint_saves")
    if not isinstance(saves, list) or not any(
        isinstance(save, dict)
        and save.get("iteration") == end_iteration
        and save.get("accounting_complete") is True
        and save.get("checkpoint_sha256") == result_checkpoint["sha256"]
        and save.get("checkpoint_programs") == result_checkpoint["programs"]
        for save in saves
    ):
        raise RoundTransactionError(
            "OpenEvolve slice witness has no post-accounting final checkpoint save"
        )

    if witness.get("openevolve_version") != "0.2.26":
        raise RoundTransactionError("unsupported OpenEvolve witness version")
    for name in (
        "openevolve_controller",
        "openevolve_process_parallel",
        "openevolve_database",
        "openevolve_api",
    ):
        source_path = witness.get(f"{name}_path")
        if not isinstance(source_path, str):
            raise RoundTransactionError(
                f"OpenEvolve slice witness is missing {name} source path"
            )
        observed = _file_descriptor(Path(source_path), f"{name} source")
        for field in ("path", "sha256", "bytes"):
            if witness.get(f"{name}_{field}") != observed[field]:
                raise RoundTransactionError(
                    f"OpenEvolve slice witness source mismatch for {name}_{field}"
                )
    if not isinstance(witness.get("completed_at"), str):
        raise RoundTransactionError(
            "OpenEvolve slice witness has no completion timestamp"
        )
    allowed_fields = set(expected) | {
        "submission_attempts",
        "outcomes",
        "successful_evaluations",
        "worker_errors",
        "checkpoint_saves",
        "openevolve_version",
        "completed_at",
    }
    for name in (
        "openevolve_controller",
        "openevolve_process_parallel",
        "openevolve_database",
        "openevolve_api",
    ):
        allowed_fields.update(
            f"{name}_{field}" for field in ("path", "sha256", "bytes")
        )
    if set(witness) != allowed_fields:
        raise RoundTransactionError(
            "OpenEvolve slice witness fields are not exact"
        )
    witness["sha256"] = _file_sha256(witness_path)
    witness["bytes"] = witness_path.stat().st_size
    return witness


def _completion_marker_expected(
    config: FlowConfig,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    launch_binding: dict[str, dict[str, Any]],
    invocation_binding: dict[str, Any],
    slice_witness: dict[str, Any],
) -> dict[str, Any]:
    base_iteration = (
        0 if base_checkpoint is None else int(base_checkpoint["last_iteration"])
    )
    expected: dict[str, Any] = {
        "schema_version": EVOLUTION_COMPLETION_SCHEMA_VERSION,
        "status": "completed",
        "output_dir": str(
            (
                config.repo_dir
                / "results"
                / "evolution"
                / f"humanize_{config.run_id}"
            ).resolve()
        ),
        "resume_checkpoint": (
            None if base_checkpoint is None else base_checkpoint["path"]
        ),
        "base_last_iteration": base_iteration,
        "iterations_requested": config.iterations_per_round,
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
        "slice_witness_path": slice_witness["path"],
        "slice_witness_sha256": slice_witness["sha256"],
        "slice_witness_bytes": slice_witness["bytes"],
    }
    for name, descriptor in launch_binding.items():
        for field in ("path", "sha256", "bytes"):
            expected[f"{name}_{field}"] = descriptor[field]
    expected.update(invocation_binding)
    return expected


def _validate_completion_marker(
    marker_path: Path,
    config: FlowConfig,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    launch_binding: dict[str, dict[str, Any]],
    invocation_binding: dict[str, Any],
    slice_witness: dict[str, Any],
) -> dict[str, Any]:
    marker = _read_json_object(marker_path, "OpenEvolve completion marker")
    witness_with_path = dict(slice_witness)
    witness_with_path["path"] = str(_slice_witness_path(marker_path.parent).resolve())
    expected = _completion_marker_expected(
        config,
        base_checkpoint,
        result_checkpoint,
        launch_binding,
        _validate_invocation_binding(
            config, invocation_binding, launch_binding
        ),
        witness_with_path,
    )
    for key, value in expected.items():
        if marker.get(key) != value:
            raise RoundTransactionError(
                f"OpenEvolve completion marker mismatch for {key}: "
                f"expected {value!r}, got {marker.get(key)!r}"
            )
    if (
        set(marker) != set(expected) | {"completed_at"}
        or not isinstance(marker.get("completed_at"), str)
    ):
        raise RoundTransactionError(
            "OpenEvolve completion marker fields are not exact"
        )
    marker["sha256"] = _file_sha256(marker_path)
    marker["bytes"] = marker_path.stat().st_size
    return marker


def _revalidate_frozen_bindings(
    config: FlowConfig,
    launch: Any,
    invocation: Any,
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    if not isinstance(launch, dict):
        raise RoundTransactionError(
            "managed OpenEvolve launch is missing its frozen launch binding"
        )
    expected_context = str(
        Path(os.path.abspath(round_dir / "search-context.md"))
    )
    context = launch.get("context")
    if (
        not isinstance(context, dict)
        or context.get("path") != expected_context
    ):
        raise RoundTransactionError(
            "managed OpenEvolve launch has the wrong frozen context"
        )
    codex_executable = (
        launch.get("codex_executable") if config.codex_cli else None
    )
    observed = _evolution_launch_binding(
        config,
        context_path=Path(expected_context),
        codex_executable=codex_executable,
    )
    if observed != launch:
        raise RoundTransactionError(
            "evolution launch inputs changed after transaction prepare"
        )
    validated_invocation = _validate_invocation_binding(
        config, invocation, observed
    )
    return observed, validated_invocation


def _current_evolution_bindings(
    config: FlowConfig,
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Describe current launch inputs without replacing the frozen context."""
    context_path = Path(os.path.abspath(round_dir / "search-context.md"))
    codex_identity: dict[str, Any] | None = None
    codex_version: str | None = None
    codex_cwd: str | None = None
    if config.codex_cli:
        codex_identity, codex_version, codex_cwd = _fresh_codex_binding(config)
    launch = _evolution_launch_binding(
        config,
        context_path=context_path,
        codex_executable=codex_identity,
    )
    invocation = _fresh_invocation_binding(
        config,
        codex_identity=codex_identity,
        codex_version=codex_version,
        codex_cwd=codex_cwd,
    )
    _validate_invocation_binding(config, invocation, launch)
    return launch, invocation


def _binding_identity_sha256(
    launch: dict[str, dict[str, Any]],
    invocation: dict[str, Any],
) -> str:
    encoded = json.dumps(
        {"launch": launch, "invocation": invocation},
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validate_stored_binding_shape(
    config: FlowConfig,
    launch: Any,
    invocation: Any,
    round_dir: Path,
    current_launch: dict[str, dict[str, Any]],
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Validate an old identity without requiring old source bytes to exist.

    A prepared transaction may safely replay after source files at the same
    canonical paths are upgraded.  The old descriptors must still be exact,
    and the round context (which is transaction data rather than source code)
    must remain byte-identical.
    """
    if not isinstance(launch, dict) or set(launch) != set(current_launch):
        raise RoundTransactionError(
            "managed OpenEvolve launch binding fields are incomplete"
        )
    for name, current in current_launch.items():
        descriptor = launch.get(name)
        expected_fields = {"path", "sha256", "bytes"}
        if name == "codex_executable":
            expected_fields.add("mode")
        if (
            not isinstance(descriptor, dict)
            or set(descriptor) != expected_fields
            or descriptor.get("path") != current["path"]
            or not isinstance(descriptor.get("sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", descriptor["sha256"]) is None
            or isinstance(descriptor.get("bytes"), bool)
            or not isinstance(descriptor.get("bytes"), int)
            or descriptor["bytes"] < 0
        ):
            raise RoundTransactionError(
                f"managed OpenEvolve {name} identity is malformed or redirected"
            )
        if name == "codex_executable" and (
            isinstance(descriptor.get("mode"), bool)
            or not isinstance(descriptor.get("mode"), int)
            or descriptor["mode"] < 0
        ):
            raise RoundTransactionError(
                "managed OpenEvolve Codex executable mode is invalid"
            )
    if launch["context"] != current_launch["context"]:
        raise RoundTransactionError(
            "evolution launch inputs changed after transaction prepare: "
            "the frozen context is not byte-identical"
        )

    if not isinstance(invocation, dict) or set(invocation) != set(
        EVOLUTION_INVOCATION_FIELDS
    ):
        raise RoundTransactionError(
            "evolution invocation binding fields are incomplete"
        )
    if invocation["model_names"] != [config.model]:
        raise RoundTransactionError("evolution model binding changed")
    if invocation["reasoning_effort"] != config.reasoning_effort:
        raise RoundTransactionError("evolution reasoning binding changed")
    if invocation["codex_cli"] is not config.codex_cli:
        raise RoundTransactionError("evolution backend selection changed")
    workers = invocation["max_parallel_evaluations"]
    if (
        isinstance(workers, bool)
        or not isinstance(workers, int)
        or workers < 1
    ):
        raise RoundTransactionError(
            "evolution worker binding identity is invalid"
        )
    api_base = invocation["api_base"]
    if (
        not isinstance(api_base, str)
        or not api_base
        or (config.api_base is not None and api_base != config.api_base)
    ):
        raise RoundTransactionError("evolution API base binding changed")
    if invocation["temperature_disabled"] is not True:
        raise RoundTransactionError(
            "managed evolution must freeze temperature-disabled mode"
        )
    if config.codex_cli:
        executable = launch["codex_executable"]
        if (
            invocation["codex_executable_mode"] != executable["mode"]
            or invocation["codex_cwd"]
            != str(config.repo_dir.resolve(strict=True))
            or not isinstance(invocation["codex_version"], str)
            or not invocation["codex_version"]
        ):
            raise RoundTransactionError(
                "Codex execution identity is malformed"
            )
    elif any(
        invocation[field] is not None
        for field in (
            "codex_version",
            "codex_cwd",
            "codex_executable_mode",
        )
    ):
        raise RoundTransactionError(
            "non-Codex invocation contains Codex execution fields"
        )
    return copy.deepcopy(launch), copy.deepcopy(invocation)


def _binding_change_reason(
    old_launch: dict[str, dict[str, Any]],
    old_invocation: dict[str, Any],
    current_launch: dict[str, dict[str, Any]],
    current_invocation: dict[str, Any],
) -> str:
    changed = [
        f"launch:{name}"
        for name in sorted(current_launch)
        if old_launch[name] != current_launch[name]
    ]
    changed.extend(
        f"invocation:{name}"
        for name in sorted(current_invocation)
        if old_invocation[name] != current_invocation[name]
    )
    return (
        "prepared OpenEvolve binding changed before source-ready: "
        + ", ".join(changed)
    )


def _frozen_bindings_from_state(
    config: FlowConfig,
    state: dict[str, Any],
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    return _revalidate_frozen_bindings(
        config,
        state.get("_evolution_launch_binding"),
        state.get("_evolution_invocation_binding"),
        round_dir,
    )


def run_openevolve(config: FlowConfig, state: dict[str, Any], round_dir: Path) -> Path:
    """Run one exact OpenEvolve increment and require a durable success marker."""
    evolution_name = f"humanize_{config.run_id}"
    output_dir = config.repo_dir / "results" / "evolution" / evolution_name
    iterations_this_round = config.iterations_per_round
    if "_evolution_base_checkpoint" not in state:
        raise RoundTransactionError(
            "managed OpenEvolve launch is missing its frozen base checkpoint"
        )
    frozen_base = state["_evolution_base_checkpoint"]
    if frozen_base is None:
        expected_base_path = None
    elif isinstance(frozen_base, dict) and isinstance(
        frozen_base.get("path"), str
    ):
        expected_base_path = frozen_base["path"]
    else:
        raise RoundTransactionError(
            "managed OpenEvolve frozen base checkpoint is invalid"
        )
    if state.get("last_checkpoint") != expected_base_path:
        raise RoundTransactionError(
            "managed OpenEvolve state disagrees with its frozen base checkpoint"
        )
    if frozen_base is None:
        base_checkpoint = None
    else:
        base_checkpoint = _checkpoint_descriptor(
            output_dir,
            Path(frozen_base["path"]),
            expected_iteration=frozen_base.get("last_iteration"),
        )
        if base_checkpoint != frozen_base:
            raise RoundTransactionError(
                "managed OpenEvolve base checkpoint changed after prepare"
            )
    base_iteration = (
        0 if base_checkpoint is None else int(base_checkpoint["last_iteration"])
    )
    expected_iteration = base_iteration + iterations_this_round
    marker_path = _completion_marker_path(round_dir)
    witness_path = _slice_witness_path(round_dir)
    for artifact in (marker_path, witness_path):
        if artifact.is_symlink() or artifact.exists():
            raise RoundTransactionError(
                f"refusing to overwrite an existing completion artifact: {artifact}"
            )

    lease_fd = state.get("_round_lifecycle_lease_fd")
    lease_path_value = state.get("_round_lifecycle_lease_path")
    expected_lease_path = _round_lifecycle_lock_path(round_dir.absolute()).absolute()
    if (
        isinstance(lease_fd, bool)
        or not isinstance(lease_fd, int)
        or lease_fd < 0
        or not isinstance(lease_path_value, str)
        or Path(lease_path_value).absolute() != expected_lease_path
    ):
        raise RoundTransactionError(
            "managed OpenEvolve launch is missing its inherited lifecycle lease"
        )
    _validate_round_lifecycle_inode(lease_fd, expected_lease_path)
    try:
        fcntl.flock(lease_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        raise RoundTransactionError(
            "managed OpenEvolve lifecycle lease is not held"
        ) from exc

    launch_binding, invocation_binding = _frozen_bindings_from_state(
        config, state, round_dir
    )
    context_path = Path(launch_binding["context"]["path"])
    command = [
        sys.executable,
        launch_binding["launcher"]["path"],
        "--run-name", evolution_name,
        "--iterations", str(iterations_this_round),
        "--models", *invocation_binding["model_names"],
        "--humanize-context", str(context_path),
        "--completion-marker", str(marker_path),
        "--slice-witness", str(witness_path),
        "--lifecycle-lease-fd", str(lease_fd),
        "--lifecycle-lease-path", str(expected_lease_path),
        "--config", launch_binding["config"]["path"],
        "--seed", launch_binding["seed"]["path"],
        "--max-parallel-evaluations",
        str(invocation_binding["max_parallel_evaluations"]),
        "--api-base", invocation_binding["api_base"],
    ]
    if invocation_binding["reasoning_effort"] is not None:
        command.extend([
            "--reasoning-effort",
            invocation_binding["reasoning_effort"],
        ])
    if invocation_binding["temperature_disabled"]:
        command.append("--no-temperature")
    if base_checkpoint is not None:
        command.extend(["--resume", base_checkpoint["path"]])
    if invocation_binding["codex_cli"]:
        command.append("--codex-cli")

    child_environment = os.environ.copy()
    if invocation_binding["codex_cli"]:
        child_environment["QCODE_CODEX_BIN"] = launch_binding[
            "codex_executable"
        ]["path"]
        child_environment["QCODE_CODEX_CWD"] = invocation_binding["codex_cwd"]
    else:
        child_environment.pop("QCODE_CODEX_BIN", None)
        child_environment.pop("QCODE_CODEX_CWD", None)
    log_path = round_dir / "evolution.log"
    with tempfile.TemporaryDirectory(
        prefix="qcode-openevolve-pycache-"
    ) as cache:
        child_environment["PYTHONPYCACHEPREFIX"] = cache
        with log_path.open("w", encoding="utf-8") as stream:
            process = subprocess.Popen(
                command,
                cwd=config.repo_dir,
                stdout=stream,
                stderr=subprocess.STDOUT,
                pass_fds=(lease_fd,),
                start_new_session=True,
                env=child_environment,
            )
            _wait_for_managed_process(process, command)

    result_checkpoint = _checkpoint_descriptor(
        output_dir,
        output_dir / "checkpoints" / f"checkpoint_{expected_iteration}",
        expected_iteration=expected_iteration,
    )
    witness = _validate_slice_witness(
        witness_path,
        config,
        base_checkpoint,
        result_checkpoint,
        launch_binding,
        invocation_binding,
    )
    _validate_completion_marker(
        marker_path,
        config,
        base_checkpoint,
        result_checkpoint,
        launch_binding,
        invocation_binding,
        witness,
    )
    return Path(result_checkpoint["path"])


_milp_is_fully_exact = is_fully_exact


def evaluate_with_milp(
    candidate: dict[str, Any],
    config: FlowConfig,
    *,
    checkpoint_path: str | Path | None = None,
    resume: bool = True,
    hard_timeout_per_logical: float | None = None,
) -> dict[str, Any]:
    """Use qcode's evaluator with durable, killable per-direction solves."""
    from evaluation.evaluator import evaluate_candidate_milp
    from evaluation.final_gate import FOM_THRESHOLD
    from main import merge_bp_milp_result

    result = evaluate_candidate_milp(
        int(candidate["ell"]),
        int(candidate["m"]),
        [tuple(map(int, term)) for term in candidate["A_terms"]],
        [tuple(map(int, term)) for term in candidate["B_terms"]],
        milp_timeout_per_logical=config.milp_timeout_per_logical,
        milp_total_timeout=config.milp_total_timeout,
        milp_early_stop=(config.milp_early_stop or None),
        milp_target_fom=FOM_THRESHOLD,
        milp_checkpoint_path=checkpoint_path,
        milp_resume=resume,
        milp_hard_timeout_per_logical=hard_timeout_per_logical,
    )
    merged = merge_bp_milp_result(candidate, result)
    # Preserve pre-MILP machine gates when an exact result replaces the BP row;
    # final acceptance requires this replayable evidence.
    for field in ("static_eligibility", "structural_novelty"):
        if field in candidate:
            merged[field] = candidate[field]
    merged["candidate_key"] = code_key(candidate)
    if "threshold_proof_witness" in result:
        merged["threshold_proof_witness"] = copy.deepcopy(
            result["threshold_proof_witness"]
        )
    merged["milp_attempted"] = True
    # A reviewer must never be able to alter this machine-derived field.
    merged["d_is_exact"] = is_fully_exact(merged)
    return merged


def _deduplicate(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    best: dict[str, dict[str, Any]] = {}
    for row in rows:
        key = code_key(row)
        current = best.get(key)
        if current is None or candidate_fom(row) > candidate_fom(current):
            best[key] = row
    return list(best.values())


def select_for_milp(
    new_elites: list[dict[str, Any]],
    archive: EliteArchive | None,
    audited_keys: set[str],
    limit: int,
    audited_digests: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Select diverse elites with one lane for high-upside BP outliers.

    The sqrt(n) credibility heuristic remains useful for budget allocation, but
    it is not a theorem and must not categorically exclude a real breakthrough.
    """
    if limit <= 0:
        return []
    archive_rows = [] if archive is None else archive.ranked()
    pool = _deduplicate(new_elites + archive_rows)
    eligible = []
    for row in pool:
        if code_key(row) in audited_keys:
            continue
        static = row.get("static_eligibility") or {}
        novelty = row.get("structural_novelty") or {}
        if static and static.get("eligible") is not True:
            continue
        if novelty and novelty.get("novel") is not True:
            continue
        digest = (
            authoritative_candidate_digest(row)
            if audited_digests
            else None
        )
        if audited_digests and digest and digest in audited_digests:
            continue
        eligible.append(row)

    credible = [row for row in eligible if credible_bp_candidate(row)]
    exploratory = [row for row in eligible if not credible_bp_candidate(row)]
    credible.sort(key=candidate_fom, reverse=True)
    exploratory.sort(key=candidate_fom, reverse=True)

    selected: list[dict[str, Any]] = []
    used_cells: set[str] = set()

    def add_from(rows: list[dict[str, Any]], target: int) -> None:
        for require_new_cell in (True, False):
            for row in rows:
                if len(selected) >= target or len(selected) >= limit:
                    return
                if row in selected:
                    continue
                cell = str(row.get("archive_cell", ""))
                if require_new_cell and cell and cell in used_cells:
                    continue
                selected.append(row)
                if cell:
                    used_cells.add(cell)

    reserve_exploration = bool(exploratory) and limit > 1
    add_from(credible, limit - int(reserve_exploration))
    if reserve_exploration:
        add_from(exploratory, len(selected) + 1)
    add_from(credible + exploratory, limit)
    return selected


def _stage1_milp_worker_count(config: FlowConfig, pending_count: int) -> int:
    """Return the Stage 1 candidate lanes allowed by the shared worker cap."""
    if pending_count < 1:
        return 0
    budget = config.max_total_workers
    if budget is None:
        budget = 3
    return min(3, budget, pending_count)


class HumanizeFlow:
    """One-build/one-review qcode loop with durable evidence and hard gates."""

    def __init__(
        self,
        config: FlowConfig,
        *,
        reviewer: Reviewer | None = None,
        evolution_runner: EvolutionRunner = run_openevolve,
        milp_evaluator: MilpEvaluator = evaluate_with_milp,
    ):
        config.validate()
        self.config = config
        self.store = RunStore.create(config.repo_dir / "results", config.run_id)
        self.archive = EliteArchive(self.store.archive_path)
        self.reviewer = reviewer or CodexReviewer(
            repo_dir=config.repo_dir,
            model=config.review_model,
            effort=config.review_effort,
        )
        self.evolution_runner = evolution_runner
        self.milp_evaluator = milp_evaluator
        self.run_dir = config.repo_dir / "results" / "runs" / self.store.run_id
        self.run_dir.mkdir(parents=True, exist_ok=True)

    @property
    def evolution_output(self) -> Path:
        return self.config.repo_dir / "results" / "evolution" / f"humanize_{self.store.run_id}"

    @property
    def candidate_log(self) -> Path:
        return self.config.candidate_file or self.evolution_output / "all_codes.jsonl"

    @staticmethod
    def _read_jsonl(path: Path) -> list[dict[str, Any]]:
        if not path.is_file():
            return []
        return [
            json.loads(line)
            for line in path.read_text().splitlines()
            if line.strip()
        ]

    @staticmethod
    def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
        atomic_write_jsonl(path, rows)

    @property
    def evaluations_path(self) -> Path:
        return self.run_dir / "evaluations.jsonl"

    def _milp_checkpoint_path(self, candidate_key: str) -> Path:
        if not candidate_key or any(
            character not in "0123456789abcdef" for character in candidate_key
        ):
            raise AuditStateError("candidate_key is unsafe for a checkpoint path")
        repo_root = self.config.repo_dir
        results_root = repo_root / "results"
        runs_root = results_root / "runs"
        for label, path in (
            ("repository", repo_root),
            ("results", results_root),
            ("runs", runs_root),
            ("run directory", self.run_dir),
        ):
            if path.is_symlink():
                raise AuditStateError(
                    f"MILP {label} may not be a symlink: {path}"
                )
            if not path.is_dir():
                raise AuditStateError(
                    f"MILP {label} is not a directory: {path}"
                )
        resolved_repo = repo_root.resolve(strict=True)
        resolved_runs = runs_root.resolve(strict=True)
        resolved_run = self.run_dir.resolve(strict=True)
        try:
            resolved_runs.relative_to(resolved_repo)
        except ValueError as exc:
            raise AuditStateError(
                f"MILP runs root escapes the repository: {resolved_runs}"
            ) from exc
        expected_run = resolved_runs / self.store.run_id
        if resolved_run != expected_run:
            raise AuditStateError(
                "MILP run directory is outside the fixed results/runs root"
            )
        checkpoint_root = self.run_dir / "milp-checkpoints"
        if checkpoint_root.is_symlink():
            raise AuditStateError(
                f"MILP checkpoint root may not be a symlink: {checkpoint_root}"
            )
        checkpoint_root.mkdir(parents=True, exist_ok=True)
        if not checkpoint_root.is_dir():
            raise AuditStateError(
                f"MILP checkpoint root is not a directory: {checkpoint_root}"
            )
        resolved_root = checkpoint_root.resolve(strict=True)
        if resolved_root.parent != resolved_run:
            raise AuditStateError(
                "MILP checkpoint root is outside the fixed run directory"
            )
        checkpoint = resolved_root / f"{candidate_key}.json"
        if checkpoint.is_symlink():
            raise AuditStateError(
                f"MILP checkpoint may not be a symlink: {checkpoint}"
            )
        if checkpoint.exists() and not checkpoint.is_file():
            raise AuditStateError(
                f"MILP checkpoint is not a regular file: {checkpoint}"
            )
        try:
            checkpoint.relative_to(resolved_root)
        except ValueError as exc:
            raise AuditStateError(
                f"MILP checkpoint escapes its root: {checkpoint}"
            ) from exc
        return checkpoint

    @staticmethod
    def _decode_canonical_jsonl(payload: bytes, path: Path) -> list[dict[str, Any]]:
        rows: list[dict[str, Any]] = []

        def reject_constant(value: str) -> None:
            raise ValueError(f"non-finite JSON number: {value}")

        def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
            value: dict[str, Any] = {}
            for key, item in pairs:
                if key in value:
                    raise ValueError(f"duplicate JSON key: {key}")
                value[key] = item
            return value

        for line_number, raw in enumerate(payload.splitlines(keepends=True), 1):
            if not raw.endswith(b"\n"):
                raise AuditStateError(
                    f"canonical evaluation line {line_number} is not terminated"
                )
            try:
                row = json.loads(
                    raw.decode("utf-8"),
                    parse_constant=reject_constant,
                    object_pairs_hook=reject_duplicates,
                )
            except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
                raise AuditStateError(
                    f"invalid canonical evaluation {path}:{line_number}: {exc}"
                ) from exc
            if not isinstance(row, dict):
                raise AuditStateError(
                    f"canonical evaluation {path}:{line_number} is not an object"
                )
            rows.append(row)
        return rows

    def _read_canonical_evaluations(
        self,
        *,
        recover_final_partial: bool,
    ) -> list[dict[str, Any]]:
        path = self.evaluations_path
        if path.is_symlink():
            raise AuditStateError(
                f"canonical evaluations may not be a symlink: {path}"
            )
        if not path.exists():
            return []
        if not path.is_file():
            raise AuditStateError(
                f"canonical evaluations must be a regular file: {path}"
            )
        payload = path.read_bytes()
        if payload and not payload.endswith(b"\n"):
            split = payload.rfind(b"\n") + 1
            prefix, tail = payload[:split], payload[split:]
            # A bad complete row before the final fragment is never repairable.
            rows = self._decode_canonical_jsonl(prefix, path)
            if not recover_final_partial:
                raise AuditStateError(
                    f"canonical evaluations end in a partial row: {path}"
                )
            digest = hashlib.sha256(tail).hexdigest()
            archive = (
                self.run_dir
                / "recovery"
                / f"evaluations-final-partial-{digest[:16]}.bin"
            )
            if archive.exists():
                if archive.is_symlink() or archive.read_bytes() != tail:
                    raise AuditStateError(
                        f"evaluation partial-row archive is inconsistent: {archive}"
                    )
            else:
                atomic_write_bytes(archive, tail)
            atomic_write_bytes(path, prefix)
            self.store.event(
                "evaluation_partial_row_recovered",
                archive=str(archive),
                bytes=len(tail),
                sha256=digest,
            )
            return rows
        return self._decode_canonical_jsonl(payload, path)

    def _rebuild_global_audit_state(
        self,
        state: dict[str, Any],
        *,
        recover_final_partial: bool,
    ) -> tuple[list[dict[str, Any]], Any]:
        rows = self._read_canonical_evaluations(
            recover_final_partial=recover_final_partial
        )
        rebuilt = rebuild_audit_state(
            rows,
            fully_exact=is_fully_exact,
            checkpoint_path_for=lambda key: self._milp_checkpoint_path(key),
        )
        state.update(rebuilt.as_state_fields())
        state["audit_evaluations_seen"] = rebuilt.evaluations_seen
        state["unresolved_count"] = len(rebuilt.unresolved)
        self.store.write_state(state)
        return rows, rebuilt

    def _trusted_exact_audit_view(
        self,
        rows: list[dict[str, Any]],
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        """Return formally replayed exact rows and the subset that are WINs."""
        from evaluation.final_gate import classify_win

        # Validate the whole append-only history before promoting any one row.
        rebuild_audit_state(
            rows,
            fully_exact=is_fully_exact,
            checkpoint_path_for=lambda key: self._milp_checkpoint_path(key),
        )
        exact_by_key: dict[str, dict[str, Any]] = {}
        for row in rows:
            if (
                classify_evaluation(
                    row,
                    fully_exact=is_fully_exact,
                )
                is AuditOutcome.EXACT
            ):
                exact_by_key[code_key(row)] = copy.deepcopy(row)

        wins_by_key: dict[str, dict[str, Any]] = {}
        for key, row in exact_by_key.items():
            try:
                result = classify_win(
                    int(row["n"]),
                    int(row["k"]),
                    int(row["d"]),
                )
            except (KeyError, TypeError, ValueError, OverflowError) as exc:
                raise AuditStateError(
                    f"trusted exact row {key} has invalid win coordinates"
                ) from exc
            if result.get("passed") is True:
                wins_by_key[key] = row

        exact = sorted(
            exact_by_key.values(),
            key=lambda row: (
                code_key(row) in wins_by_key,
                candidate_fom(row),
                code_key(row),
            ),
            reverse=True,
        )
        wins = [row for row in exact if code_key(row) in wins_by_key]
        return exact, wins

    @staticmethod
    def _record_trusted_audit_view(
        state: dict[str, Any],
        exact: list[dict[str, Any]],
        wins: list[dict[str, Any]],
    ) -> None:
        state["trusted_exact_count"] = len(exact)
        state["trusted_win_count"] = len(wins)
        state["best_exact_fom"] = max(
            (candidate_fom(row) for row in exact),
            default=0.0,
        )

    @staticmethod
    def _canonical_row_identity(row: dict[str, Any]) -> str:
        try:
            payload = json.dumps(
                row,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            raise AuditStateError(
                "evaluation row must be strict JSON data"
            ) from exc
        return hashlib.sha256(payload).hexdigest()

    def _reconcile_round_evaluations(
        self,
        selected: list[dict[str, Any]],
        *,
        round_number: int,
        milp_path: Path,
        global_rows: list[dict[str, Any]],
    ) -> list[dict[str, Any]]:
        selected_keys = [code_key(row) for row in selected]
        selected_key_set = set(selected_keys)
        current: dict[str, dict[str, Any]] = {}
        global_identities = {
            self._canonical_row_identity(row) for row in global_rows
        }
        for row in global_rows:
            attempt = row.get("audit_attempt")
            if not isinstance(attempt, dict) or attempt.get("round") != round_number:
                continue
            key = code_key(row)
            if key not in selected_key_set:
                continue
            if key in current:
                raise AuditStateError(
                    f"candidate {key} has duplicate attempts in round {round_number}"
                )
            current[key] = row

        # Legacy round rows may not have audit_attempt. Trust them only if the
        # byte-equivalent logical row is already present in the global log. A
        # malformed or partial round file is evidence, so archive its exact
        # bytes before replacing it from the canonical global log.
        legacy_round_rows: list[dict[str, Any]] = []
        if milp_path.is_symlink():
            raise AuditStateError(
                f"round evaluations may not be a symlink: {milp_path}"
            )
        if milp_path.exists():
            if not milp_path.is_file():
                raise AuditStateError(
                    f"round evaluations must be a regular file: {milp_path}"
                )
            raw_round = milp_path.read_bytes()
            try:
                legacy_round_rows = self._decode_canonical_jsonl(
                    raw_round, milp_path
                )
            except AuditStateError:
                digest = hashlib.sha256(raw_round).hexdigest()
                archive = (
                    milp_path.parent
                    / f"milp-malformed-{digest[:16]}.bin"
                )
                if archive.is_symlink():
                    raise AuditStateError(
                        f"round evaluation archive may not be a symlink: {archive}"
                    )
                if archive.exists():
                    if not archive.is_file() or archive.read_bytes() != raw_round:
                        raise AuditStateError(
                            "round evaluation archive is inconsistent: "
                            f"{archive}"
                        )
                else:
                    atomic_write_bytes(archive, raw_round)
                self.store.event(
                    "round_evaluations_archived",
                    round=round_number,
                    archive=str(archive),
                    bytes=len(raw_round),
                    sha256=digest,
                )
        for row in legacy_round_rows:
            key = code_key(row)
            if (
                key in selected_key_set
                and key not in current
                and self._canonical_row_identity(row) in global_identities
            ):
                current[key] = row

        ordered = [current[key] for key in selected_keys if key in current]
        atomic_write_jsonl(milp_path, ordered)
        return ordered

    def _select_audit_candidates(
        self,
        candidates: list[dict[str, Any]],
        state: dict[str, Any],
        *,
        screened_history: list[dict[str, Any]] | None = None,
    ) -> list[dict[str, Any]]:
        if self.config.milp_top <= 0:
            return []
        unresolved = state.get("unresolved_candidates", {})
        if not isinstance(unresolved, dict):
            raise AuditStateError("unresolved_candidates must be an object")
        retry_entries = select_retry_lane(
            unresolved,
            limit=self.config.milp_top if unresolved else 0,
        )
        retry_candidates = [dict(entry["candidate"]) for entry in retry_entries]
        blocked_keys = set(state.get("audited_keys", [])) | set(unresolved)
        blocked_digests = set(state.get("audited_structural_digests", []))
        blocked_digests.update(
            str(entry["canonical_digest"])
            for entry in unresolved.values()
            if entry.get("canonical_digest")
        )
        # Drain the retry queue before admitting new candidates.  Mixing one
        # retry with fresh work lets a persistent timeout queue grow by up to
        # milp_top-1 entries per round, so Stage 1 can exhaust max_rounds even
        # though every retry is making progress under its larger budget.
        if unresolved:
            return retry_candidates
        if screened_history is None:
            screened_history, _rejected = (
                self._replay_screened_candidate_pool(candidates)
            )
        new_candidates = select_for_milp(
            screened_history,
            None,
            blocked_keys,
            self.config.milp_top,
            blocked_digests,
        )
        return retry_candidates + new_candidates

    def _attempt_plan(
        self,
        candidate: dict[str, Any],
        state: dict[str, Any],
        *,
        round_number: int,
    ) -> tuple[FlowConfig, dict[str, Any], dict[str, Any]]:
        key = code_key(candidate)
        unresolved = state.get("unresolved_candidates", {})
        entry = unresolved.get(key) if isinstance(unresolved, dict) else None
        completed = 0 if entry is None else int(entry["attempts_completed"])
        base_hard_timeout = max(
            float(self.config.milp_timeout_per_logical) * 1.1,
            float(self.config.milp_timeout_per_logical) + 30.0,
        )
        budget = retry_budget(
            timeout_per_logical=self.config.milp_timeout_per_logical,
            total_timeout=self.config.milp_total_timeout,
            completed_attempts=completed,
            hard_timeout_per_logical=base_hard_timeout,
        )
        assert budget.hard_timeout_per_logical is not None
        checkpoint = self._milp_checkpoint_path(key)
        checkpoint.parent.mkdir(parents=True, exist_ok=True)
        attempt = {
            "schema_version": 1,
            "round": round_number,
            "kind": "new" if completed == 0 else "retry",
            "attempt": completed + 1,
            "multiplier": budget.multiplier,
            "soft": budget.timeout_per_logical,
            "total": budget.total_timeout,
            "hard": budget.hard_timeout_per_logical,
            "checkpoint": str(checkpoint),
        }
        attempt_config = replace(
            self.config,
            milp_timeout_per_logical=budget.timeout_per_logical,
            milp_total_timeout=budget.total_timeout,
        )
        invocation = {
            "checkpoint_path": str(checkpoint),
            "resume": True,
            "hard_timeout_per_logical": budget.hard_timeout_per_logical,
        }
        return attempt_config, attempt, invocation

    def _evaluate_audit_attempt(
        self,
        candidate: dict[str, Any],
        attempt_config: FlowConfig,
        invocation: dict[str, Any],
    ) -> dict[str, Any]:
        formal_contract = False
        try:
            signature = inspect.signature(self.milp_evaluator)
            signature.bind(candidate, attempt_config, **invocation)
        except TypeError:
            try:
                signature.bind(candidate, attempt_config)
            except TypeError as exc:
                raise AuditStateError(
                    "MILP evaluator accepts neither the production invocation "
                    "nor the legacy two-argument contract"
                ) from exc
            if not self.config.allow_debug_audit_evaluator:
                raise AuditStateError(
                    "legacy two-argument MILP evaluator is disabled; set "
                    "allow_debug_audit_evaluator only for explicit debug runs"
                )
            result = self.milp_evaluator(candidate, attempt_config)
        else:
            result = self.milp_evaluator(
                candidate,
                attempt_config,
                **invocation,
            )
            formal_contract = True
        if not isinstance(result, dict):
            raise AuditStateError("MILP evaluator must return an object")
        returned = dict(result)
        formal_result = (
            formal_contract
            and "audit_evaluator_invocation" in returned
        )
        if (
            not formal_result
            and not self.config.allow_debug_audit_evaluator
        ):
            raise AuditStateError(
                "MILP evaluator did not return the formal schema-v2 audit "
                "invocation contract; debug downgrade is disabled"
            )
        returned["_humanize_formal_audit_contract"] = formal_result
        if not formal_contract:
            returned.pop("audit_evaluator_invocation", None)
        return returned

    @staticmethod
    def _transaction_paths(round_dir: Path) -> dict[str, Path]:
        return {
            "manifest": round_dir / "evolution-transaction.json",
            "batch": round_dir / "candidate-batch.jsonl",
            "completion": _completion_marker_path(round_dir),
            "witness": _slice_witness_path(round_dir),
        }

    @staticmethod
    def _prepared_transaction_has_no_bound_source(
        transaction: dict[str, Any],
    ) -> bool:
        return (
            transaction.get("status") == "prepared"
            and transaction.get("result_checkpoint") is None
            and transaction.get("candidate_end_offset") is None
            and transaction.get("candidate_source_sha256") is None
            and transaction.get("candidate_source_rows") is None
            and transaction.get("candidate_batch_identity") is None
            and transaction.get("completion_marker_sha256") is None
            and transaction.get("completion_witness_sha256") is None
            and "source_ready_at" not in transaction
            and "batch_ready_at" not in transaction
            and "committed_at" not in transaction
        )

    def _validate_binding_rebind_history(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        current_launch: dict[str, dict[str, Any]],
    ) -> list[dict[str, Any]]:
        history = transaction.setdefault("evolution_binding_rebinds", [])
        if not isinstance(history, list):
            raise RoundTransactionError(
                "transaction evolution binding rebind history is invalid"
            )
        if transaction["mode"] != "openevolve":
            if history:
                raise RoundTransactionError(
                    "candidate-file transaction contains binding rebind history"
                )
            return history

        pending_seen = False
        previous_launch: dict[str, dict[str, Any]] | None = None
        previous_invocation: dict[str, Any] | None = None
        required = {
            "attempt",
            "status",
            "reason",
            "old_launch_binding",
            "old_invocation_binding",
            "old_binding_sha256",
            "candidate_start_offset",
            "evolution_attempts_before",
            "abandoned_ranges_before",
            "abandoned_checkpoints_before",
            "planned_at",
        }
        completed_only = {
            "new_launch_binding",
            "new_invocation_binding",
            "new_binding_sha256",
            "evolution_attempts_after",
            "abandoned_ranges_after",
            "abandoned_checkpoints_after",
            "rebound_at",
        }
        for index, record in enumerate(history, 1):
            if not isinstance(record, dict):
                raise RoundTransactionError(
                    "evolution binding rebind record is not an object"
                )
            status = record.get("status")
            expected_fields = (
                required
                if status == "rebinding"
                else required | completed_only
                if status == "rebound"
                else set()
            )
            if not expected_fields or set(record) != expected_fields:
                raise RoundTransactionError(
                    "evolution binding rebind record fields are invalid"
                )
            if (
                record["attempt"] != index
                or not isinstance(record["reason"], str)
                or not record["reason"]
                or record["candidate_start_offset"]
                != transaction["candidate_start_offset"]
                or not isinstance(record["planned_at"], str)
                or any(
                    isinstance(record[field], bool)
                    or not isinstance(record[field], int)
                    or record[field] < 0
                    for field in (
                        "evolution_attempts_before",
                        "abandoned_ranges_before",
                        "abandoned_checkpoints_before",
                    )
                )
            ):
                raise RoundTransactionError(
                    "evolution binding rebind record identity is invalid"
                )
            old_launch, old_invocation = _validate_stored_binding_shape(
                self.config,
                record["old_launch_binding"],
                record["old_invocation_binding"],
                round_dir,
                current_launch,
            )
            if record["old_binding_sha256"] != _binding_identity_sha256(
                old_launch, old_invocation
            ):
                raise RoundTransactionError(
                    "old evolution binding rebind identity changed"
                )
            if previous_launch is not None and (
                old_launch != previous_launch
                or old_invocation != previous_invocation
            ):
                raise RoundTransactionError(
                    "evolution binding rebind history is not a continuous chain"
                )

            if status == "rebinding":
                if pending_seen or index != len(history):
                    raise RoundTransactionError(
                        "pending evolution binding rebind must be last"
                    )
                pending_seen = True
                previous_launch = old_launch
                previous_invocation = old_invocation
            else:
                new_launch, new_invocation = _validate_stored_binding_shape(
                    self.config,
                    record["new_launch_binding"],
                    record["new_invocation_binding"],
                    round_dir,
                    current_launch,
                )
                if record["new_binding_sha256"] != _binding_identity_sha256(
                    new_launch, new_invocation
                ):
                    raise RoundTransactionError(
                        "new evolution binding rebind identity changed"
                    )
                if (
                    not isinstance(record["rebound_at"], str)
                    or any(
                        isinstance(record[field], bool)
                        or not isinstance(record[field], int)
                        or record[field] < record[before]
                        for field, before in (
                            (
                                "evolution_attempts_after",
                                "evolution_attempts_before",
                            ),
                            (
                                "abandoned_ranges_after",
                                "abandoned_ranges_before",
                            ),
                            (
                                "abandoned_checkpoints_after",
                                "abandoned_checkpoints_before",
                            ),
                        )
                    )
                ):
                    raise RoundTransactionError(
                        "completed evolution binding rebind record is invalid"
                    )
                previous_launch = new_launch
                previous_invocation = new_invocation

        if history and (
            transaction.get("launch_binding") != previous_launch
            or transaction.get("invocation_binding") != previous_invocation
        ):
            raise RoundTransactionError(
                "transaction binding disagrees with its rebind history"
            )
        if pending_seen and (
            transaction["status"] != "prepared"
            or not self._prepared_transaction_has_no_bound_source(transaction)
        ):
            raise RoundTransactionError(
                "pending evolution binding rebind crossed source-ready"
            )
        return history

    def _rebind_prepared_evolution_transaction(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        current_launch: dict[str, dict[str, Any]],
        current_invocation: dict[str, Any],
    ) -> None:
        """Replayably abandon an unfinished slice and bind current sources."""
        if not self._prepared_transaction_has_no_bound_source(transaction):
            raise RoundTransactionError(
                "only an unbound prepared OpenEvolve transaction may rebind"
            )
        batch_path = Path(transaction["candidate_batch"])
        if batch_path.is_symlink() or batch_path.exists():
            raise RoundTransactionError(
                "prepared OpenEvolve transaction contains an unbound "
                "candidate batch"
            )
        history = transaction["evolution_binding_rebinds"]
        pending = (
            history[-1]
            if history and history[-1].get("status") == "rebinding"
            else None
        )
        if pending is None:
            old_launch = copy.deepcopy(transaction["launch_binding"])
            old_invocation = copy.deepcopy(transaction["invocation_binding"])
            pending = {
                "attempt": len(history) + 1,
                "status": "rebinding",
                "reason": _binding_change_reason(
                    old_launch,
                    old_invocation,
                    current_launch,
                    current_invocation,
                ),
                "old_launch_binding": old_launch,
                "old_invocation_binding": old_invocation,
                "old_binding_sha256": _binding_identity_sha256(
                    old_launch, old_invocation
                ),
                "candidate_start_offset": transaction[
                    "candidate_start_offset"
                ],
                "evolution_attempts_before": len(
                    transaction["evolution_attempts"]
                ),
                "abandoned_ranges_before": len(
                    transaction["abandoned_ranges"]
                ),
                "abandoned_checkpoints_before": len(
                    transaction["abandoned_checkpoints"]
                ),
                "planned_at": utc_now(),
            }
            history.append(pending)
            atomic_write_json(
                self._transaction_paths(round_dir)["manifest"], transaction
            )

        self._abandon_uncommitted_tail(transaction, round_dir)
        expected_path = (
            self.evolution_output
            / "checkpoints"
            / f"checkpoint_{int(transaction['expected_result_iteration'])}"
        )
        self._resume_checkpoint_quarantine(
            transaction, round_dir, expected_path
        )
        self._quarantine_untrusted_evolution_attempt(
            transaction,
            round_dir,
            expected_path,
            reason=pending["reason"],
        )

        new_launch, new_invocation = _current_evolution_bindings(
            self.config, round_dir
        )
        pending.update({
            "status": "rebound",
            "new_launch_binding": copy.deepcopy(new_launch),
            "new_invocation_binding": copy.deepcopy(new_invocation),
            "new_binding_sha256": _binding_identity_sha256(
                new_launch, new_invocation
            ),
            "evolution_attempts_after": len(
                transaction["evolution_attempts"]
            ),
            "abandoned_ranges_after": len(
                transaction["abandoned_ranges"]
            ),
            "abandoned_checkpoints_after": len(
                transaction["abandoned_checkpoints"]
            ),
            "rebound_at": utc_now(),
        })
        transaction["launch_binding"] = copy.deepcopy(new_launch)
        transaction["invocation_binding"] = copy.deepcopy(new_invocation)
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )

    def _load_transaction(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
        *,
        allow_prepared_rebind: bool = False,
    ) -> dict[str, Any] | None:
        paths = self._transaction_paths(round_dir)
        if not paths["manifest"].exists():
            return None
        transaction = _read_json_object(
            paths["manifest"], "round transaction manifest"
        )
        expected_mode = (
            "candidate-file" if self.config.candidate_file is not None
            else "openevolve"
        )
        identity = {
            "schema_version": ROUND_TRANSACTION_SCHEMA_VERSION,
            "protocol_version": ROUND_TRANSACTION_PROTOCOL_VERSION,
            "run_id": self.store.run_id,
            "round": number,
            "mode": expected_mode,
            "candidate_log": str(self.candidate_log.resolve()),
            "candidate_batch": str(paths["batch"].resolve()),
            "completion_marker": (
                None
                if expected_mode == "candidate-file"
                else str(paths["completion"].resolve())
            ),
            "completion_witness": (
                None
                if expected_mode == "candidate-file"
                else str(paths["witness"].resolve())
            ),
        }
        for key, expected in identity.items():
            if transaction.get(key) != expected:
                raise RoundTransactionError(
                    f"round transaction identity mismatch for {key}: "
                    f"expected {expected!r}, got {transaction.get(key)!r}"
                )
        status = transaction.get("status")
        if status not in {"prepared", "source-ready", "batch-ready", "committed"}:
            raise RoundTransactionError(
                f"invalid round transaction status: {status!r}"
            )
        start_offset = transaction.get("candidate_start_offset")
        initial_offset = transaction.get("initial_candidate_offset")
        if (
            isinstance(start_offset, bool)
            or not isinstance(start_offset, int)
            or start_offset < 0
            or isinstance(initial_offset, bool)
            or not isinstance(initial_offset, int)
            or initial_offset < 0
            or start_offset != initial_offset
        ):
            raise RoundTransactionError("transaction candidate offsets are invalid")
        if not isinstance(transaction.get("abandoned_ranges"), list):
            raise RoundTransactionError("transaction abandoned_ranges is invalid")
        partial_recoveries = transaction.setdefault(
            "candidate_partial_recoveries", []
        )
        if not isinstance(partial_recoveries, list):
            raise RoundTransactionError(
                "transaction candidate_partial_recoveries is invalid"
            )
        if not isinstance(transaction.get("evolution_attempts"), list):
            raise RoundTransactionError("transaction evolution_attempts is invalid")
        if not isinstance(transaction.get("abandoned_checkpoints"), list):
            raise RoundTransactionError("transaction abandoned_checkpoints is invalid")
        rebinds = transaction.setdefault("evolution_binding_rebinds", [])
        if not isinstance(rebinds, list):
            raise RoundTransactionError(
                "transaction evolution binding rebind history is invalid"
            )
        if int(state.get("current_round", -1)) != number - 1:
            raise RoundTransactionError(
                "round transaction does not follow the durable current_round"
            )

        base = transaction.get("base_checkpoint")
        if expected_mode == "candidate-file":
            if (
                base is not None
                or transaction.get("expected_result_iteration") is not None
                or transaction.get("launch_binding") is not None
                or transaction.get("invocation_binding") is not None
                or rebinds
            ):
                raise RoundTransactionError(
                    "candidate-file transaction may not contain evolution bindings"
                )
        else:
            if base is not None:
                if not isinstance(base, dict) or "path" not in base:
                    raise RoundTransactionError("transaction base checkpoint is invalid")
                observed = _checkpoint_descriptor(
                    self.evolution_output,
                    Path(base["path"]),
                    expected_iteration=base.get("last_iteration"),
                )
                if observed != base:
                    raise RoundTransactionError("base checkpoint changed after prepare")
        expected_iteration = transaction.get("expected_result_iteration")
        if expected_mode == "openevolve":
            base_iteration = 0 if base is None else int(base["last_iteration"])
            if (
                transaction.get("iterations_per_round")
                != self.config.iterations_per_round
                or expected_iteration
                != base_iteration + self.config.iterations_per_round
            ):
                raise RoundTransactionError(
                    "transaction does not request one exact iteration increment"
                )
            current_launch, current_invocation = _current_evolution_bindings(
                self.config, round_dir
            )
            stored_launch, stored_invocation = (
                _validate_stored_binding_shape(
                    self.config,
                    transaction.get("launch_binding"),
                    transaction.get("invocation_binding"),
                    round_dir,
                    current_launch,
                )
            )
            history = self._validate_binding_rebind_history(
                transaction, round_dir, current_launch
            )
            pending_rebind = bool(
                history and history[-1].get("status") == "rebinding"
            )
            launch_changed = stored_launch != current_launch
            if pending_rebind or launch_changed:
                if (
                    status != "prepared"
                    or not allow_prepared_rebind
                ):
                    _revalidate_frozen_bindings(
                        self.config,
                        stored_launch,
                        stored_invocation,
                        round_dir,
                    )
                    raise RoundTransactionError(
                        "pending prepared evolution binding rebind requires "
                        "its lifecycle lease"
                    )
                self._rebind_prepared_evolution_transaction(
                    transaction,
                    round_dir,
                    current_launch,
                    current_invocation,
                )
            _revalidate_frozen_bindings(
                self.config,
                transaction.get("launch_binding"),
                transaction.get("invocation_binding"),
                round_dir,
            )
        return transaction

    def _prepare_transaction(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
    ) -> dict[str, Any]:
        paths = self._transaction_paths(round_dir)
        if paths["manifest"].is_symlink() or paths["manifest"].exists():
            raise RoundTransactionError(
                "cannot prepare a transaction over an existing manifest"
            )
        for label in ("batch", "completion", "witness"):
            if paths[label].is_symlink() or paths[label].exists():
                raise RoundTransactionError(
                    f"transaction artifact exists without manifest: {paths[label]}"
                )
        start_offset = state.get("candidate_offset", 0)
        if (
            isinstance(start_offset, bool)
            or not isinstance(start_offset, int)
            or start_offset < 0
        ):
            raise RoundTransactionError("state candidate_offset is invalid")
        if self.candidate_log.is_file():
            source_size = self.candidate_log.stat().st_size
            if start_offset > source_size:
                raise RoundTransactionError(
                    "candidate log is shorter than the durable offset"
                )
        elif start_offset:
            raise RoundTransactionError(
                "candidate log is missing at a non-zero durable offset"
            )

        mode = (
            "candidate-file" if self.config.candidate_file is not None
            else "openevolve"
        )
        base_checkpoint = None
        launch_binding = None
        invocation_binding = None
        expected_iteration = None
        if mode == "openevolve":
            checkpoint_value = state.get("last_checkpoint")
            if checkpoint_value:
                base_checkpoint = _checkpoint_descriptor(
                    self.evolution_output, Path(checkpoint_value)
                )
            base_iteration = (
                0
                if base_checkpoint is None
                else int(base_checkpoint["last_iteration"])
            )
            expected_iteration = base_iteration + self.config.iterations_per_round
            expected_path = (
                self.evolution_output
                / "checkpoints"
                / f"checkpoint_{expected_iteration}"
            )
            _assert_checkpoint_frontier(
                self.evolution_output,
                base_iteration,
            )
            _quarantine_orphan_round_context(round_dir)
            launch_binding, invocation_binding = _fresh_evolution_bindings(
                self.config, state, round_dir
            )
        elif state.get("last_checkpoint") is not None:
            raise RoundTransactionError(
                "candidate-file transaction inherited an evolution checkpoint"
            )

        transaction: dict[str, Any] = {
            "schema_version": ROUND_TRANSACTION_SCHEMA_VERSION,
            "protocol_version": ROUND_TRANSACTION_PROTOCOL_VERSION,
            "run_id": self.store.run_id,
            "round": number,
            "mode": mode,
            "status": "prepared",
            "iterations_per_round": (
                self.config.iterations_per_round if mode == "openevolve" else 0
            ),
            "base_checkpoint": base_checkpoint,
            "expected_result_iteration": expected_iteration,
            "result_checkpoint": None,
            "launch_binding": launch_binding,
            "invocation_binding": invocation_binding,
            "candidate_log": str(self.candidate_log.resolve()),
            "initial_candidate_offset": start_offset,
            "candidate_start_offset": start_offset,
            "candidate_end_offset": None,
            "abandoned_ranges": [],
            "candidate_partial_recoveries": [],
            "abandoned_checkpoints": [],
            "evolution_attempts": [],
            "evolution_binding_rebinds": [],
            "candidate_source_sha256": None,
            "candidate_source_rows": None,
            "candidate_batch": str(paths["batch"].resolve()),
            "candidate_batch_identity": None,
            "completion_marker": (
                None if mode == "candidate-file" else str(paths["completion"].resolve())
            ),
            "completion_marker_sha256": None,
            "completion_witness": (
                None if mode == "candidate-file" else str(paths["witness"].resolve())
            ),
            "completion_witness_sha256": None,
            "prepared_at": utc_now(),
        }
        if mode == "candidate-file":
            source_end = (
                self.candidate_log.stat().st_size
                if self.candidate_log.is_file()
                else 0
            )
            try:
                source_rows, observed_end, source_sha256 = read_jsonl_range(
                    self.candidate_log, start_offset, source_end
                )
            except ValueError as exc:
                raise RoundTransactionError(str(exc)) from exc
            transaction["candidate_end_offset"] = observed_end
            transaction["candidate_source_sha256"] = source_sha256
            transaction["candidate_source_rows"] = len(source_rows)
            transaction["status"] = "source-ready"
            transaction["source_ready_at"] = utc_now()

        atomic_write_json(paths["manifest"], transaction)
        return transaction

    def _validate_transaction_source(
        self,
        transaction: dict[str, Any],
    ) -> list[dict[str, Any]]:
        end_offset = transaction.get("candidate_end_offset")
        if (
            isinstance(end_offset, bool)
            or not isinstance(end_offset, int)
            or end_offset < int(transaction["candidate_start_offset"])
        ):
            raise RoundTransactionError("transaction end offset is invalid")
        try:
            rows, observed_end, source_sha256 = read_jsonl_range(
                self.candidate_log,
                int(transaction["candidate_start_offset"]),
                end_offset,
            )
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        if (
            observed_end != end_offset
            or source_sha256 != transaction.get("candidate_source_sha256")
            or len(rows) != transaction.get("candidate_source_rows")
        ):
            raise RoundTransactionError(
                "candidate source slice changed after transaction prepare"
            )
        return rows

    def _validate_transaction_checkpoint(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> dict[str, Any] | None:
        if transaction["mode"] == "candidate-file":
            return None
        result = transaction.get("result_checkpoint")
        if not isinstance(result, dict) or "path" not in result:
            raise RoundTransactionError("transaction result checkpoint is missing")
        observed = _checkpoint_descriptor(
            self.evolution_output,
            Path(result["path"]),
            expected_iteration=transaction["expected_result_iteration"],
        )
        if observed != result:
            raise RoundTransactionError("result checkpoint changed after completion")
        witness_path = _slice_witness_path(round_dir)
        witness = _validate_slice_witness(
            witness_path,
            self.config,
            transaction.get("base_checkpoint"),
            observed,
            transaction.get("launch_binding"),
            transaction.get("invocation_binding"),
        )
        if witness["sha256"] != transaction.get("completion_witness_sha256"):
            raise RoundTransactionError("completion witness changed after prepare")
        marker_path = _completion_marker_path(round_dir)
        marker = _validate_completion_marker(
            marker_path,
            self.config,
            transaction.get("base_checkpoint"),
            observed,
            transaction.get("launch_binding"),
            transaction.get("invocation_binding"),
            witness,
        )
        if marker["sha256"] != transaction.get("completion_marker_sha256"):
            raise RoundTransactionError("completion marker changed after prepare")
        return observed

    def _validate_candidate_batch(
        self,
        transaction: dict[str, Any],
    ) -> list[dict[str, Any]]:
        identity = transaction.get("candidate_batch_identity")
        batch_path = Path(transaction["candidate_batch"])
        if (
            not isinstance(identity, dict)
            or batch_path.is_symlink()
            or not batch_path.is_file()
        ):
            raise RoundTransactionError("candidate batch is missing")
        observed = {
            "sha256": _file_sha256(batch_path),
            "bytes": batch_path.stat().st_size,
            "rows": identity.get("rows"),
        }
        try:
            rows, end_offset, source_sha256 = read_jsonl_range(batch_path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        observed["rows"] = len(rows)
        if end_offset != observed["bytes"] or source_sha256 != observed["sha256"]:
            raise RoundTransactionError("candidate batch byte identity is invalid")
        if observed != {
            "sha256": identity.get("sha256"),
            "bytes": identity.get("bytes"),
            "rows": identity.get("rows"),
        }:
            raise RoundTransactionError("candidate batch changed after commit")
        return rows

    @staticmethod
    def _candidate_rows_identity(rows: list[dict[str, Any]]) -> dict[str, Any]:
        payload = "".join(
            json.dumps(row, ensure_ascii=False, default=str) + "\n"
            for row in rows
        ).encode("utf-8")
        return {
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
            "rows": len(rows),
        }

    def _candidate_log_size(self, *, start_offset: int) -> int:
        path = self.candidate_log
        if path.is_symlink():
            raise RoundTransactionError(f"candidate log may not be a symlink: {path}")
        if not path.exists():
            if start_offset == 0:
                return 0
            raise RoundTransactionError(
                "candidate log is missing at a non-zero transaction offset"
            )
        if not path.is_file():
            raise RoundTransactionError(f"candidate log is not a regular file: {path}")
        size = path.stat().st_size
        if size < start_offset:
            raise RoundTransactionError(
                "candidate log is shorter than the transaction start offset"
            )
        return size

    @staticmethod
    def _inspect_abandoned_payload(
        payload: bytes,
        *,
        start_offset: int,
    ) -> dict[str, Any]:
        complete_length = payload.rfind(b"\n") + 1
        complete_rows = 0
        for raw in payload[:complete_length].splitlines(keepends=True):
            try:
                row = json.loads(raw.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise RoundTransactionError(
                    f"invalid complete JSONL record in abandoned tail: {exc}"
                ) from exc
            if not isinstance(row, dict):
                raise RoundTransactionError(
                    "non-object JSONL record in abandoned candidate tail"
                )
            complete_rows += 1
        return {
            "start_offset": start_offset,
            "end_offset": start_offset + len(payload),
            "last_complete_offset": start_offset + complete_length,
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
            "complete_rows": complete_rows,
            "partial_bytes": len(payload) - complete_length,
        }

    @staticmethod
    def _abandoned_candidate_batch_path(
        round_dir: Path,
        attempt_number: int,
    ) -> Path:
        return (
            round_dir
            / f"abandoned-candidate-complete-{attempt_number:03d}.jsonl"
        )

    def _materialize_abandoned_candidate_batch(
        self,
        round_dir: Path,
        attempt_number: int,
        payload: bytes,
        tail: dict[str, Any],
    ) -> tuple[Path, dict[str, Any]]:
        """Materialize the complete JSONL prefix of an abandoned raw tail."""
        complete_length = (
            int(tail["last_complete_offset"]) - int(tail["start_offset"])
        )
        complete_payload = payload[:complete_length]
        batch_path = self._abandoned_candidate_batch_path(
            round_dir, attempt_number
        )
        if batch_path.is_symlink():
            raise RoundTransactionError(
                f"abandoned candidate batch may not be a symlink: {batch_path}"
            )
        expected = {
            "path": str(batch_path.resolve()),
            "sha256": hashlib.sha256(complete_payload).hexdigest(),
            "bytes": len(complete_payload),
            "rows": int(tail["complete_rows"]),
        }
        if batch_path.exists():
            descriptor = _file_descriptor(
                batch_path, "abandoned complete candidate batch"
            )
            observed = {
                **descriptor,
                "rows": int(tail["complete_rows"]),
            }
            if observed != expected or batch_path.read_bytes() != complete_payload:
                raise RoundTransactionError(
                    "abandoned complete candidate batch changed"
                )
        else:
            descriptor = atomic_write_bytes(batch_path, complete_payload)
            observed = {
                "path": str(batch_path.resolve()),
                **descriptor,
                "rows": int(tail["complete_rows"]),
            }
            if observed != expected:
                raise RoundTransactionError(
                    "abandoned complete candidate batch identity is inconsistent"
                )
        try:
            rows, end_offset, source_sha256 = read_jsonl_range(batch_path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        if (
            len(rows) != expected["rows"]
            or end_offset != expected["bytes"]
            or source_sha256 != expected["sha256"]
        ):
            raise RoundTransactionError(
                "abandoned complete candidate batch is not valid bound JSONL"
            )
        return batch_path, expected

    def _abandoned_candidate_inputs(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> tuple[Path, ...]:
        """Validate and return salvaged complete rows in attempt order.

        Pre-hotfix manifests did not record the derived batch descriptor.  Their
        immutable raw archive already binds the exact bytes, so materializing
        the complete prefix remains a safe, backward-compatible migration.
        """
        inputs: list[Path] = []
        abandoned = transaction.get("abandoned_ranges", [])
        if not isinstance(abandoned, list):
            raise RoundTransactionError("transaction abandoned_ranges is invalid")
        start_offset = int(transaction["candidate_start_offset"])
        for attempt_number, record in enumerate(abandoned, 1):
            if not isinstance(record, dict):
                raise RoundTransactionError(
                    "abandoned-tail record is not an object"
                )
            archive_path = (
                round_dir
                / f"abandoned-candidate-tail-{attempt_number:03d}.bin"
            )
            descriptor = _file_descriptor(
                archive_path, "abandoned candidate-tail archive"
            )
            payload = archive_path.read_bytes()
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            expected_archive = {
                **tail,
                "archive_path": descriptor["path"],
                "archive_sha256": descriptor["sha256"],
                "archive_bytes": descriptor["bytes"],
            }
            for key, value in expected_archive.items():
                if record.get(key) != value:
                    raise RoundTransactionError(
                        f"abandoned-tail record mismatch for {key}"
                    )
            batch_path, batch_identity = (
                self._materialize_abandoned_candidate_batch(
                    round_dir,
                    attempt_number,
                    payload,
                    tail,
                )
            )
            recorded_identity = record.get("complete_candidate_batch")
            if (
                recorded_identity is not None
                and recorded_identity != batch_identity
            ):
                raise RoundTransactionError(
                    "abandoned complete candidate batch binding mismatch"
                )
            if batch_identity["rows"]:
                inputs.append(batch_path)
        return tuple(inputs)

    def _atomic_restore_candidate_prefix(self, start_offset: int) -> None:
        path = self.candidate_log
        if start_offset == 0 and not path.exists():
            return
        try:
            _rows, observed, _sha256 = read_jsonl_range(path, 0, start_offset)
        except ValueError as exc:
            raise RoundTransactionError(
                "durable candidate prefix is not valid JSONL"
            ) from exc
        if observed != start_offset:
            raise RoundTransactionError("candidate prefix length changed during recovery")
        with path.open("rb") as stream:
            prefix = stream.read(start_offset)
            if len(prefix) != start_offset:
                raise RoundTransactionError(
                    "candidate log changed while restoring its durable prefix"
                )
        atomic_write_bytes(path, prefix)
        if path.stat().st_size != start_offset:
            raise RoundTransactionError("candidate log prefix restore was not durable")

    def _validate_candidate_partial_recoveries(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> None:
        history = transaction.get("candidate_partial_recoveries", [])
        if not isinstance(history, list):
            raise RoundTransactionError(
                "transaction candidate_partial_recoveries is invalid"
            )
        start_offset = int(transaction["candidate_start_offset"])
        for recovery_number, record in enumerate(history, 1):
            if not isinstance(record, dict):
                raise RoundTransactionError(
                    "candidate partial recovery record is not an object"
                )
            archive_path = (
                round_dir
                / f"candidate-final-partial-{recovery_number:03d}.bin"
            )
            descriptor = _file_descriptor(
                archive_path, "candidate partial-tail archive"
            )
            payload = archive_path.read_bytes()
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            if tail["partial_bytes"] < 1:
                raise RoundTransactionError(
                    "candidate partial-tail archive has no partial record"
                )
            expected = {
                **tail,
                "archive_path": descriptor["path"],
                "archive_sha256": descriptor["sha256"],
                "archive_bytes": descriptor["bytes"],
            }
            for key, value in expected.items():
                if record.get(key) != value:
                    raise RoundTransactionError(
                        f"candidate partial recovery mismatch for {key}"
                    )

    def _recover_final_partial_candidate_tail(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> int:
        """Archive and remove only an unterminated final candidate record.

        The archive contains the entire transaction tail, not just the fragment.
        This makes an interruption between archive creation, atomic truncation,
        and manifest publication unambiguous on the next resume.
        """
        self._validate_candidate_partial_recoveries(transaction, round_dir)
        history = transaction.setdefault("candidate_partial_recoveries", [])
        start_offset = int(transaction["candidate_start_offset"])
        recovery_number = len(history) + 1
        archive_path = (
            round_dir / f"candidate-final-partial-{recovery_number:03d}.bin"
        )
        if archive_path.is_symlink():
            raise RoundTransactionError(
                f"candidate partial-tail archive may not be a symlink: {archive_path}"
            )
        source_size = self._candidate_log_size(start_offset=start_offset)

        if archive_path.exists():
            descriptor = _file_descriptor(
                archive_path, "orphan candidate partial-tail archive"
            )
            payload = archive_path.read_bytes()
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            if tail["partial_bytes"] < 1:
                raise RoundTransactionError(
                    "orphan candidate partial-tail archive has no fragment"
                )
            complete_length = (
                int(tail["last_complete_offset"]) - start_offset
            )
            if source_size == tail["end_offset"]:
                with self.candidate_log.open("rb") as stream:
                    stream.seek(start_offset)
                    observed = stream.read()
                if observed != payload:
                    raise RoundTransactionError(
                        "orphan candidate partial-tail archive disagrees "
                        "with candidate log"
                    )
                self._atomic_restore_candidate_prefix(
                    int(tail["last_complete_offset"])
                )
            elif source_size == tail["last_complete_offset"]:
                with self.candidate_log.open("rb") as stream:
                    stream.seek(start_offset)
                    observed = stream.read(complete_length)
                if observed != payload[:complete_length]:
                    raise RoundTransactionError(
                        "recovered candidate prefix disagrees with its "
                        "partial-tail archive"
                    )
            else:
                raise RoundTransactionError(
                    "cannot reconcile orphan candidate partial-tail archive "
                    "with candidate log"
                )
        else:
            if source_size == start_offset:
                return source_size
            with self.candidate_log.open("rb") as stream:
                observed_size = os.fstat(stream.fileno()).st_size
                stream.seek(start_offset)
                payload = stream.read()
                final_size = os.fstat(stream.fileno()).st_size
            if observed_size != source_size or final_size != source_size:
                raise RoundTransactionError(
                    "candidate log changed while inspecting its final record"
                )
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            if tail["partial_bytes"] == 0:
                return source_size
            descriptor = atomic_write_bytes(archive_path, payload)
            descriptor["path"] = str(archive_path.resolve())
            self._atomic_restore_candidate_prefix(
                int(tail["last_complete_offset"])
            )

        if (
            descriptor["sha256"] != tail["sha256"]
            or descriptor["bytes"] != tail["bytes"]
        ):
            raise RoundTransactionError(
                "candidate partial-tail archive identity mismatch"
            )
        record = {
            **tail,
            "archive_path": descriptor["path"],
            "archive_sha256": descriptor["sha256"],
            "archive_bytes": descriptor["bytes"],
            "reason": "unterminated final candidate JSONL record",
            "recovered_at": utc_now(),
        }
        history.append(record)
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )
        return int(tail["last_complete_offset"])

    def _abandon_uncommitted_tail(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> None:
        """Archive and atomically remove raw rows not bound to a checkpoint."""
        start_offset = int(transaction["candidate_start_offset"])
        abandoned = transaction["abandoned_ranges"]
        attempt_number = len(abandoned) + 1
        archive_path = (
            round_dir / f"abandoned-candidate-tail-{attempt_number:03d}.bin"
        )
        if archive_path.is_symlink():
            raise RoundTransactionError(
                f"abandoned-tail archive may not be a symlink: {archive_path}"
            )
        source_size = self._candidate_log_size(start_offset=start_offset)

        if archive_path.exists():
            descriptor = _file_descriptor(
                archive_path, "orphan abandoned-tail archive"
            )
            payload = archive_path.read_bytes()
            if not payload:
                raise RoundTransactionError(
                    "orphan abandoned-tail archive is unexpectedly empty"
                )
            if source_size == start_offset:
                pass
            elif source_size == start_offset + len(payload):
                with self.candidate_log.open("rb") as stream:
                    stream.seek(start_offset)
                    observed = stream.read()
                if observed != payload:
                    raise RoundTransactionError(
                        "orphan abandoned-tail archive disagrees with candidate log"
                    )
                self._atomic_restore_candidate_prefix(start_offset)
            else:
                raise RoundTransactionError(
                    "cannot reconcile orphan abandoned-tail archive with candidate log"
                )
        else:
            if source_size == start_offset:
                return
            with self.candidate_log.open("rb") as stream:
                observed_size = os.fstat(stream.fileno()).st_size
                stream.seek(start_offset)
                payload = stream.read()
                final_size = os.fstat(stream.fileno()).st_size
            if observed_size != source_size or final_size != source_size:
                raise RoundTransactionError(
                    "candidate log changed while archiving its abandoned tail"
                )
            descriptor = atomic_write_bytes(archive_path, payload)
            descriptor["path"] = str(archive_path.resolve())
            self._atomic_restore_candidate_prefix(start_offset)

        tail = self._inspect_abandoned_payload(
            payload,
            start_offset=start_offset,
        )
        if descriptor["sha256"] != tail["sha256"] or descriptor["bytes"] != tail["bytes"]:
            raise RoundTransactionError("abandoned-tail archive identity mismatch")
        _batch_path, batch_identity = self._materialize_abandoned_candidate_batch(
            round_dir,
            attempt_number,
            payload,
            tail,
        )
        tail.update({
            "archive_path": descriptor["path"],
            "archive_sha256": descriptor["sha256"],
            "archive_bytes": descriptor["bytes"],
            "complete_candidate_batch": batch_identity,
            "reason": "expected checkpoint absent before safe replay",
            "abandoned_at": utc_now(),
        })
        abandoned.append(tail)
        atomic_write_json(self._transaction_paths(round_dir)["manifest"], transaction)

    @staticmethod
    def _checkpoint_quarantine_paths(
        round_dir: Path,
        expected_checkpoint: Path,
        attempt: int,
    ) -> tuple[dict[str, Path], dict[str, Path]]:
        sources = {
            "checkpoint": expected_checkpoint,
            "completion_marker": _completion_marker_path(round_dir),
            "slice_witness": _slice_witness_path(round_dir),
        }
        destinations = {
            "checkpoint": round_dir / f"abandoned-checkpoint-attempt-{attempt:03d}",
            "completion_marker": round_dir / (
                f"abandoned-completion-marker-attempt-{attempt:03d}.json"
            ),
            "slice_witness": round_dir / (
                f"abandoned-slice-witness-attempt-{attempt:03d}.json"
            ),
        }
        return sources, destinations

    def _resume_checkpoint_quarantine(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        expected_checkpoint: Path,
    ) -> None:
        """Finish a content-bound write-ahead quarantine after interruption."""
        records = transaction["abandoned_checkpoints"]
        pending = [
            index
            for index, record in enumerate(records)
            if isinstance(record, dict)
            and record.get("status") == "quarantining"
        ]
        last_is_pending = bool(
            records
            and isinstance(records[-1], dict)
            and records[-1].get("status") == "quarantining"
        )
        attempt = len(records) if last_is_pending else len(records) + 1
        _sources, destinations = self._checkpoint_quarantine_paths(
            round_dir, expected_checkpoint, attempt
        )
        orphan_destination = any(
            path.is_symlink() or path.exists()
            for path in destinations.values()
        )
        if orphan_destination and not pending:
            raise RoundTransactionError(
                "checkpoint quarantine destination exists without a "
                "write-ahead record"
            )
        if pending:
            self._quarantine_untrusted_evolution_attempt(
                transaction,
                round_dir,
                expected_checkpoint,
                reason="recovered interrupted checkpoint quarantine",
            )

    def _quarantine_untrusted_evolution_attempt(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        expected_checkpoint: Path,
        *,
        reason: str,
    ) -> None:
        """Durably quarantine one attempt using a replayable write-ahead record."""
        records = transaction["abandoned_checkpoints"]
        artifact_order = ("checkpoint", "completion_marker", "slice_witness")
        pending_indexes = [
            index
            for index, record in enumerate(records)
            if isinstance(record, dict)
            and record.get("status") == "quarantining"
        ]
        if pending_indexes:
            if pending_indexes != [len(records) - 1]:
                raise RoundTransactionError(
                    "checkpoint quarantine write-ahead record is not last"
                )
            plan = records[-1]
            attempt = len(records)
            if (
                plan.get("attempt") != attempt
                or not isinstance(plan.get("reason"), str)
                or not isinstance(plan.get("planned_at"), str)
                or plan.get("expected_checkpoint")
                != str(expected_checkpoint.absolute())
            ):
                raise RoundTransactionError(
                    "checkpoint quarantine write-ahead record is invalid"
                )
            names = plan.get("artifact_names")
            identities = plan.get("artifact_identities")
            if (
                not isinstance(names, list)
                or not names
                or any(name not in artifact_order for name in names)
                or any(not isinstance(name, str) for name in names)
                or len(names) != len(set(names))
                or names
                != [name for name in artifact_order if name in set(names)]
                or not isinstance(identities, dict)
                or set(identities) != set(names)
                or any(
                    not isinstance(identity, dict)
                    for identity in identities.values()
                )
            ):
                raise RoundTransactionError(
                    "checkpoint quarantine artifact plan is invalid"
                )
        else:
            if any(
                isinstance(record, dict) and "status" in record
                for record in records
            ):
                raise RoundTransactionError(
                    "checkpoint quarantine record has an invalid status"
                )
            attempt = len(records) + 1
            plan = None

        sources, destinations = self._checkpoint_quarantine_paths(
            round_dir, expected_checkpoint, attempt
        )
        for name in artifact_order:
            if sources[name].is_symlink() or destinations[name].is_symlink():
                raise RoundTransactionError(
                    f"refusing to quarantine symlinked OpenEvolve {name} artifact"
                )

        observed_names = [
            name
            for name in artifact_order
            if sources[name].exists() or destinations[name].exists()
        ]
        if plan is None:
            if not observed_names:
                return
            if any(destinations[name].exists() for name in artifact_order):
                raise RoundTransactionError(
                    "checkpoint quarantine destination exists without a "
                    "write-ahead record"
                )
            identities: dict[str, dict[str, Any]] = {}
            for name in observed_names:
                identity = _quarantined_artifact_descriptor(
                    sources[name], f"planned OpenEvolve {name}"
                )
                identity["path"] = str(destinations[name].resolve())
                identities[name] = identity
            plan = {
                "attempt": attempt,
                "status": "quarantining",
                "reason": reason,
                "expected_checkpoint": str(expected_checkpoint.absolute()),
                "artifact_names": observed_names,
                "artifact_identities": identities,
                "planned_at": utc_now(),
            }
            records.append(plan)
            atomic_write_json(
                self._transaction_paths(round_dir)["manifest"], transaction
            )
        else:
            planned_names = list(plan["artifact_names"])
            unexpected_names = [
                name for name in observed_names if name not in planned_names
            ]
            if unexpected_names:
                raise RoundTransactionError(
                    "unexpected OpenEvolve artifacts appeared during "
                    "checkpoint quarantine: " + ", ".join(unexpected_names)
                )

        artifacts: dict[str, dict[str, Any]] = {}
        for name in plan["artifact_names"]:
            source = sources[name]
            destination = destinations[name]
            source_present = source.exists()
            destination_present = destination.exists()
            if source_present and destination_present:
                raise RoundTransactionError(
                    f"cannot reconcile source and quarantined {name} artifacts"
                )
            if not source_present and not destination_present:
                raise RoundTransactionError(
                    f"planned OpenEvolve {name} artifact disappeared during quarantine"
                )
            observed_path = source if source_present else destination
            observed_identity = _quarantined_artifact_descriptor(
                observed_path, f"replayed OpenEvolve {name}"
            )
            observed_identity["path"] = str(destination.resolve())
            expected_identity = plan["artifact_identities"][name]
            if observed_identity != expected_identity:
                raise RoundTransactionError(
                    f"planned OpenEvolve {name} artifact identity changed "
                    "during quarantine"
                )
            if source_present:
                source_parent = source.parent
                source.replace(destination)
                _fsync_directory(source_parent)
                if destination.parent != source_parent:
                    _fsync_directory(destination.parent)
                destination_present = True
            if destination_present:
                destination_identity = _quarantined_artifact_descriptor(
                    destination, f"quarantined OpenEvolve {name}"
                )
                if destination_identity != expected_identity:
                    raise RoundTransactionError(
                        f"quarantined OpenEvolve {name} artifact identity "
                        "does not match its write-ahead record"
                    )
                artifacts[name] = destination_identity
        records[-1] = {
            "attempt": attempt,
            "reason": plan["reason"],
            "artifacts": artifacts,
            "abandoned_at": utc_now(),
        }
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )

    def _complete_prepared_evolution(
        self,
        state: dict[str, Any],
        transaction: dict[str, Any],
        round_dir: Path,
        lease: _RoundLifecycleLease,
    ) -> None:
        expected_iteration = int(transaction["expected_result_iteration"])
        expected_path = (
            self.evolution_output
            / "checkpoints"
            / f"checkpoint_{expected_iteration}"
        )
        marker_path = _completion_marker_path(round_dir)
        witness_path = _slice_witness_path(round_dir)
        base = transaction.get("base_checkpoint")
        base_iteration = 0 if base is None else int(base["last_iteration"])
        self._resume_checkpoint_quarantine(
            transaction, round_dir, expected_path
        )
        _assert_checkpoint_frontier(
            self.evolution_output,
            base_iteration,
            allowed_iterations=frozenset({expected_iteration}),
        )
        checkpoint_present = expected_path.is_symlink() or expected_path.exists()
        marker_present = marker_path.is_symlink() or marker_path.exists()
        witness_present = witness_path.is_symlink() or witness_path.exists()

        for artifact in (expected_path, marker_path, witness_path):
            if artifact.is_symlink():
                raise RoundTransactionError(
                    f"OpenEvolve completion artifact may not be a symlink: {artifact}"
                )

        if checkpoint_present and marker_present and witness_present:
            result_checkpoint = _checkpoint_descriptor(
                self.evolution_output,
                expected_path,
                expected_iteration=expected_iteration,
            )
            witness = _validate_slice_witness(
                witness_path,
                self.config,
                transaction.get("base_checkpoint"),
                result_checkpoint,
                transaction["launch_binding"],
                transaction["invocation_binding"],
            )
            marker = _validate_completion_marker(
                marker_path,
                self.config,
                transaction.get("base_checkpoint"),
                result_checkpoint,
                transaction["launch_binding"],
                transaction["invocation_binding"],
                witness,
            )
            transaction["result_checkpoint"] = result_checkpoint
            transaction["completion_witness_sha256"] = witness["sha256"]
            transaction["completion_marker_sha256"] = marker["sha256"]
            return
        if any((checkpoint_present, marker_present, witness_present)):
            self._quarantine_untrusted_evolution_attempt(
                transaction,
                round_dir,
                expected_path,
                reason=(
                    "incomplete OpenEvolve checkpoint/marker/witness artifact set"
                ),
            )

        self._abandon_uncommitted_tail(transaction, round_dir)
        transaction["evolution_attempts"].append({
            "attempt": len(transaction["evolution_attempts"]) + 1,
            "candidate_start_offset": transaction["candidate_start_offset"],
            "started_at": utc_now(),
        })
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )
        runner_state = dict(state)
        runner_state["_round_lifecycle_lease_fd"] = lease.fd
        runner_state["_round_lifecycle_lease_path"] = str(lease.path)
        runner_state["_evolution_launch_binding"] = copy.deepcopy(
            transaction["launch_binding"]
        )
        runner_state["_evolution_invocation_binding"] = copy.deepcopy(
            transaction["invocation_binding"]
        )
        runner_state["_evolution_base_checkpoint"] = copy.deepcopy(
            transaction["base_checkpoint"]
        )
        returned = self.evolution_runner(
            self.config, runner_state, round_dir
        )
        _assert_checkpoint_frontier(
            self.evolution_output,
            base_iteration,
            allowed_iterations=frozenset({expected_iteration}),
        )
        result_checkpoint = _checkpoint_descriptor(
            self.evolution_output,
            expected_path,
            expected_iteration=expected_iteration,
        )
        if returned is not None and Path(returned).resolve() != Path(
            result_checkpoint["path"]
        ):
            raise RoundTransactionError(
                "evolution runner returned the wrong checkpoint"
            )
        witness = _validate_slice_witness(
            witness_path,
            self.config,
            transaction.get("base_checkpoint"),
            result_checkpoint,
            transaction["launch_binding"],
            transaction["invocation_binding"],
        )
        marker = _validate_completion_marker(
            marker_path,
            self.config,
            transaction.get("base_checkpoint"),
            result_checkpoint,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            witness,
        )
        transaction["result_checkpoint"] = result_checkpoint
        transaction["completion_witness_sha256"] = witness["sha256"]
        transaction["completion_marker_sha256"] = marker["sha256"]

    def _capture_round_candidates(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
    ) -> list[dict[str, Any]]:
        if self.config.candidate_file is not None:
            return self._capture_round_candidates_locked(
                state, number, round_dir, None
            )
        with _acquire_round_lifecycle_lease(round_dir) as lease:
            return self._capture_round_candidates_locked(
                state, number, round_dir, lease
            )

    def _capture_round_candidates_locked(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
        lease: _RoundLifecycleLease | None,
    ) -> list[dict[str, Any]]:
        paths = self._transaction_paths(round_dir)
        transaction = self._load_transaction(
            state,
            number,
            round_dir,
            allow_prepared_rebind=lease is not None,
        )
        if transaction is None:
            transaction = self._prepare_transaction(state, number, round_dir)

        if transaction["status"] == "prepared":
            if transaction["mode"] == "openevolve":
                if lease is None:
                    raise RoundTransactionError(
                        "OpenEvolve transaction recovery requires its lifecycle lease"
                    )
                self._complete_prepared_evolution(
                    state, transaction, round_dir, lease
                )

            source_end = (
                self._recover_final_partial_candidate_tail(
                    transaction, round_dir
                )
                if transaction["mode"] == "openevolve"
                else self._candidate_log_size(
                    start_offset=int(transaction["candidate_start_offset"])
                )
            )
            try:
                source_rows, observed_end, source_sha256 = read_jsonl_range(
                    self.candidate_log,
                    int(transaction["candidate_start_offset"]),
                    source_end,
                )
            except ValueError as exc:
                raise RoundTransactionError(str(exc)) from exc
            transaction["candidate_end_offset"] = observed_end
            transaction["candidate_source_sha256"] = source_sha256
            transaction["candidate_source_rows"] = len(source_rows)
            transaction["status"] = "source-ready"
            transaction["source_ready_at"] = utc_now()
            atomic_write_json(paths["manifest"], transaction)

        if transaction["status"] in {"source-ready", "batch-ready", "committed"}:
            self._validate_transaction_checkpoint(transaction, round_dir)
            source_rows = self._validate_transaction_source(transaction)
        else:
            raise RoundTransactionError(
                f"transaction did not reach source-ready: {transaction['status']!r}"
            )

        batch_rows = _deduplicate(source_rows)
        expected_batch_identity = self._candidate_rows_identity(batch_rows)
        if transaction["status"] == "source-ready":
            batch_path = paths["batch"]
            if batch_path.is_symlink():
                raise RoundTransactionError(
                    f"candidate batch may not be a symlink: {batch_path}"
                )
            if batch_path.exists():
                try:
                    observed_rows, observed_end, observed_sha256 = read_jsonl_range(
                        batch_path, 0
                    )
                except ValueError as exc:
                    raise RoundTransactionError(str(exc)) from exc
                observed_identity = {
                    "sha256": observed_sha256,
                    "bytes": observed_end,
                    "rows": len(observed_rows),
                }
                if (
                    observed_identity != expected_batch_identity
                    or observed_rows != batch_rows
                ):
                    raise RoundTransactionError(
                        "unbound candidate batch disagrees with source snapshot"
                    )
                batch_identity = observed_identity
            else:
                batch_identity = atomic_write_jsonl(batch_path, batch_rows)
                if batch_identity != expected_batch_identity:
                    raise RoundTransactionError(
                        "atomic candidate batch identity is inconsistent"
                    )
            transaction["candidate_batch_identity"] = batch_identity
            transaction["status"] = "batch-ready"
            transaction["batch_ready_at"] = utc_now()
            atomic_write_json(paths["manifest"], transaction)

        if transaction["status"] in {"batch-ready", "committed"}:
            self._validate_transaction_checkpoint(transaction, round_dir)
            self._validate_transaction_source(transaction)
            observed_batch = self._validate_candidate_batch(transaction)
            if observed_batch != batch_rows:
                raise RoundTransactionError(
                    "candidate batch no longer matches its bound source"
                )

        initial_offset = int(transaction["initial_candidate_offset"])
        end_offset = int(transaction["candidate_end_offset"])
        base = transaction.get("base_checkpoint")
        result = transaction.get("result_checkpoint")
        expected_base = None if base is None else base["path"]
        expected_result = None if result is None else result["path"]
        precommit = (
            state.get("candidate_offset") == initial_offset
            and state.get("last_checkpoint") == expected_base
            and state.get("pending_round") is None
            and state.get("round_phase") is None
        )
        postcommit = (
            state.get("candidate_offset") == end_offset
            and state.get("last_checkpoint") == expected_result
            and state.get("pending_round") == number
            and state.get("round_phase")
            in {"screen", "audit", "review", "finalize"}
            and state.get("round_transaction_version")
            == ROUND_TRANSACTION_PROTOCOL_VERSION
        )

        if transaction["status"] == "batch-ready":
            if precommit:
                state["candidate_offset"] = end_offset
                state["last_checkpoint"] = expected_result
                state["pending_round"] = number
                state["round_phase"] = "screen"
                state["round_transaction_version"] = (
                    ROUND_TRANSACTION_PROTOCOL_VERSION
                )
                self.store.write_state(state)
                postcommit = True
            elif not postcommit:
                raise RoundTransactionError(
                    "durable state is neither before nor after transaction commit"
                )
            transaction["status"] = "committed"
            transaction["committed_at"] = utc_now()
            atomic_write_json(paths["manifest"], transaction)
        elif transaction["status"] == "committed" and not postcommit:
            raise RoundTransactionError(
                "committed manifest disagrees with durable round state"
            )

        return self._validate_candidate_batch(transaction)

    def _validate_completed_transaction(
        self,
        number: int,
        round_dir: Path,
    ) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        """Replay every binding of a committed v2 transaction without state."""
        paths = self._transaction_paths(round_dir)
        transaction = _read_json_object(
            paths["manifest"], "completed round transaction"
        )
        expected_mode = (
            "candidate-file" if self.config.candidate_file is not None
            else "openevolve"
        )
        fixed_identity = {
            "schema_version": ROUND_TRANSACTION_SCHEMA_VERSION,
            "protocol_version": ROUND_TRANSACTION_PROTOCOL_VERSION,
            "run_id": self.store.run_id,
            "round": number,
            "mode": expected_mode,
            "status": "committed",
            "candidate_log": str(self.candidate_log.resolve()),
            "candidate_batch": str(paths["batch"].resolve()),
            "completion_marker": (
                None
                if expected_mode == "candidate-file"
                else str(paths["completion"].resolve())
            ),
            "completion_witness": (
                None
                if expected_mode == "candidate-file"
                else str(paths["witness"].resolve())
            ),
        }
        for key, value in fixed_identity.items():
            if transaction.get(key) != value:
                raise RoundTransactionError(
                    f"completed transaction identity mismatch for {key}"
                )

        initial_offset = transaction.get("initial_candidate_offset")
        start_offset = transaction.get("candidate_start_offset")
        end_offset = transaction.get("candidate_end_offset")
        if (
            isinstance(initial_offset, bool)
            or not isinstance(initial_offset, int)
            or initial_offset < 0
            or start_offset != initial_offset
            or isinstance(end_offset, bool)
            or not isinstance(end_offset, int)
            or end_offset < initial_offset
        ):
            raise RoundTransactionError(
                "completed transaction candidate offsets are invalid"
            )
        if (
            isinstance(transaction.get("candidate_source_rows"), bool)
            or not isinstance(transaction.get("candidate_source_rows"), int)
            or transaction["candidate_source_rows"] < 0
            or not isinstance(transaction.get("candidate_source_sha256"), str)
            or len(transaction["candidate_source_sha256"]) != 64
        ):
            raise RoundTransactionError(
                "completed transaction source identity is invalid"
            )

        abandoned = transaction.get("abandoned_ranges")
        partial_recoveries = transaction.get(
            "candidate_partial_recoveries", []
        )
        quarantined = transaction.get("abandoned_checkpoints")
        attempts = transaction.get("evolution_attempts")
        rebinds = transaction.setdefault("evolution_binding_rebinds", [])
        if (
            not isinstance(abandoned, list)
            or not isinstance(partial_recoveries, list)
            or not isinstance(quarantined, list)
            or not isinstance(attempts, list)
            or not isinstance(rebinds, list)
        ):
            raise RoundTransactionError(
                "completed transaction recovery history is invalid"
            )
        self._abandoned_candidate_inputs(transaction, round_dir)
        self._validate_candidate_partial_recoveries(transaction, round_dir)
        for index, record in enumerate(quarantined, 1):
            if (
                not isinstance(record, dict)
                or record.get("attempt") != index
                or not isinstance(record.get("reason"), str)
                or not isinstance(record.get("abandoned_at"), str)
                or not isinstance(record.get("artifacts"), dict)
            ):
                raise RoundTransactionError(
                    "quarantined checkpoint record is invalid"
                )
            destinations = {
                "checkpoint": round_dir / f"abandoned-checkpoint-attempt-{index:03d}",
                "completion_marker": round_dir / (
                    f"abandoned-completion-marker-attempt-{index:03d}.json"
                ),
                "slice_witness": round_dir / (
                    f"abandoned-slice-witness-attempt-{index:03d}.json"
                ),
            }
            artifacts = record["artifacts"]
            if not artifacts or not set(artifacts).issubset(destinations):
                raise RoundTransactionError(
                    "quarantined checkpoint artifact set is invalid"
                )
            for name, expected_descriptor in artifacts.items():
                observed_descriptor = _quarantined_artifact_descriptor(
                    destinations[name], f"quarantined OpenEvolve {name}"
                )
                if observed_descriptor != expected_descriptor:
                    raise RoundTransactionError(
                        f"quarantined checkpoint artifact changed: {name}"
                    )
        for index, attempt in enumerate(attempts, 1):
            if (
                not isinstance(attempt, dict)
                or attempt.get("attempt") != index
                or attempt.get("candidate_start_offset") != initial_offset
                or not isinstance(attempt.get("started_at"), str)
            ):
                raise RoundTransactionError(
                    "completed transaction evolution attempt history is invalid"
                )

        base = transaction.get("base_checkpoint")
        result = transaction.get("result_checkpoint")
        if expected_mode == "candidate-file":
            if (
                transaction.get("iterations_per_round") != 0
                or base is not None
                or result is not None
                or transaction.get("expected_result_iteration") is not None
                or transaction.get("launch_binding") is not None
                or transaction.get("invocation_binding") is not None
                or transaction.get("completion_marker_sha256") is not None
                or transaction.get("completion_witness_sha256") is not None
                or abandoned
                or partial_recoveries
                or quarantined
                or attempts
                or rebinds
            ):
                raise RoundTransactionError(
                    "completed candidate-file transaction has evolution fields"
                )
        else:
            current_launch, _current_invocation = (
                _current_evolution_bindings(self.config, round_dir)
            )
            _validate_stored_binding_shape(
                self.config,
                transaction.get("launch_binding"),
                transaction.get("invocation_binding"),
                round_dir,
                current_launch,
            )
            self._validate_binding_rebind_history(
                transaction, round_dir, current_launch
            )
            _revalidate_frozen_bindings(
                self.config,
                transaction.get("launch_binding"),
                transaction.get("invocation_binding"),
                round_dir,
            )
            if base is not None:
                if not isinstance(base, dict) or "path" not in base:
                    raise RoundTransactionError(
                        "completed transaction base checkpoint is invalid"
                    )
                observed_base = _checkpoint_descriptor(
                    self.evolution_output,
                    Path(base["path"]),
                    expected_iteration=base.get("last_iteration"),
                )
                if observed_base != base:
                    raise RoundTransactionError(
                        "completed transaction base checkpoint changed"
                    )
            base_iteration = 0 if base is None else int(base["last_iteration"])
            expected_iteration = base_iteration + self.config.iterations_per_round
            if (
                transaction.get("iterations_per_round")
                != self.config.iterations_per_round
                or transaction.get("expected_result_iteration")
                != expected_iteration
                or not isinstance(result, dict)
                or result.get("last_iteration") != expected_iteration
            ):
                raise RoundTransactionError(
                    "completed transaction iteration binding is invalid"
                )
            self._validate_transaction_checkpoint(transaction, round_dir)

        source_rows = self._validate_transaction_source(transaction)
        batch_rows = self._validate_candidate_batch(transaction)
        if batch_rows != _deduplicate(source_rows):
            raise RoundTransactionError(
                "completed candidate batch disagrees with its source slice"
            )
        return transaction, batch_rows

    @staticmethod
    def _legacy_batch_paths(round_dir: Path) -> dict[str, Path]:
        return {
            "batch": round_dir / "legacy-candidate-batch.jsonl",
            "sidecar": round_dir / "legacy-candidate-batch.json",
        }

    def _validate_legacy_batch_sidecar(
        self,
        number: int,
        round_dir: Path,
    ) -> Path:
        paths = self._legacy_batch_paths(round_dir)
        sidecar = _read_json_object(
            paths["sidecar"], "legacy candidate-batch sidecar"
        )
        expected = {
            "schema_version": LEGACY_BATCH_SCHEMA_VERSION,
            "protocol": "legacy-materialized-v1",
            "status": "committed",
            "run_id": self.store.run_id,
            "round": number,
            "candidate_batch": str(paths["batch"].resolve()),
        }
        for key, value in expected.items():
            if sidecar.get(key) != value:
                raise RoundTransactionError(
                    f"legacy candidate-batch sidecar mismatch for {key}"
                )
        identity = sidecar.get("candidate_batch_identity")
        pseudo_transaction = {
            "candidate_batch": sidecar["candidate_batch"],
            "candidate_batch_identity": identity,
        }
        self._validate_candidate_batch(pseudo_transaction)
        return paths["batch"]

    def _materialize_legacy_batch(
        self,
        number: int,
        round_dir: Path,
        candidate_path: Path,
        *,
        binding: dict[str, Any],
    ) -> Path:
        paths = self._legacy_batch_paths(round_dir)
        if paths["sidecar"].is_symlink():
            raise RoundTransactionError(
                f"legacy batch sidecar may not be a symlink: {paths['sidecar']}"
            )
        if paths["sidecar"].exists():
            return self._validate_legacy_batch_sidecar(number, round_dir)
        if candidate_path.is_symlink() or not candidate_path.is_file():
            raise RoundTransactionError(
                f"legacy round candidates are missing: {candidate_path}"
            )
        try:
            rows, source_bytes, source_sha256 = read_jsonl_range(candidate_path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        source_identity = {
            "path": str(candidate_path.resolve()),
            "sha256": source_sha256,
            "bytes": source_bytes,
            "rows": len(rows),
        }
        expected_batch_identity = self._candidate_rows_identity(rows)
        if paths["batch"].is_symlink():
            raise RoundTransactionError(
                f"legacy candidate batch may not be a symlink: {paths['batch']}"
            )
        if paths["batch"].exists():
            try:
                observed_rows, observed_bytes, observed_sha256 = read_jsonl_range(
                    paths["batch"], 0
                )
            except ValueError as exc:
                raise RoundTransactionError(str(exc)) from exc
            batch_identity = {
                "sha256": observed_sha256,
                "bytes": observed_bytes,
                "rows": len(observed_rows),
            }
            if batch_identity != expected_batch_identity or observed_rows != rows:
                raise RoundTransactionError(
                    "orphan legacy candidate batch disagrees with candidates"
                )
        else:
            batch_identity = atomic_write_jsonl(paths["batch"], rows)
            if batch_identity != expected_batch_identity:
                raise RoundTransactionError(
                    "legacy candidate batch identity is inconsistent"
                )
        sidecar = {
            "schema_version": LEGACY_BATCH_SCHEMA_VERSION,
            "protocol": "legacy-materialized-v1",
            "status": "committed",
            "run_id": self.store.run_id,
            "round": number,
            "candidate_source": source_identity,
            "candidate_batch": str(paths["batch"].resolve()),
            "candidate_batch_identity": batch_identity,
            "legacy_binding": binding,
            "materialized_at": utc_now(),
        }
        atomic_write_json(paths["sidecar"], sidecar)
        return self._validate_legacy_batch_sidecar(number, round_dir)

    def _migrate_legacy_completed_rounds(self, state: dict[str, Any]) -> None:
        for number in range(1, int(state.get("current_round", 0)) + 1):
            round_dir = self.store.round_dir(number)
            manifest = self._transaction_paths(round_dir)["manifest"]
            legacy_sidecar = self._legacy_batch_paths(round_dir)["sidecar"]
            if manifest.exists():
                self._validate_completed_transaction(number, round_dir)
                continue
            if legacy_sidecar.exists():
                self._validate_legacy_batch_sidecar(number, round_dir)
                continue
            self._materialize_legacy_batch(
                number,
                round_dir,
                round_dir / "candidates.jsonl",
                binding={
                    "kind": "completed-pre-transaction-round",
                    "migrated_from_state_round": state.get("current_round"),
                },
            )

    def _validate_legacy_pending_round(
        self,
        state: dict[str, Any],
        number: int,
        candidate_path: Path,
        milp_path: Path,
    ) -> None:
        phase = state.get("round_phase")
        if phase not in {"screen", "audit", "review", "finalize"}:
            raise RoundTransactionError(
                f"legacy pending round has invalid phase: {phase!r}"
            )
        offset = state.get("candidate_offset")
        if isinstance(offset, bool) or not isinstance(offset, int) or offset < 0:
            raise RoundTransactionError("legacy candidate_offset is invalid")
        try:
            _rows, observed_offset, _sha256 = read_jsonl_range(
                self.candidate_log, 0, offset
            )
        except ValueError as exc:
            raise RoundTransactionError(
                "legacy candidate offset does not bind a valid source prefix"
            ) from exc
        if observed_offset != offset:
            raise RoundTransactionError("legacy candidate offset changed")

        checkpoint_binding = None
        if self.config.candidate_file is None:
            checkpoint_value = state.get("last_checkpoint")
            if not checkpoint_value:
                raise RoundTransactionError(
                    "legacy pending evolution round has no checkpoint"
                )
            checkpoint_binding = _checkpoint_descriptor(
                self.evolution_output,
                Path(checkpoint_value),
                expected_iteration=number * self.config.iterations_per_round,
            )
        elif state.get("last_checkpoint") is not None:
            raise RoundTransactionError(
                "legacy candidate-file round unexpectedly has a checkpoint"
            )

        if phase in {"audit", "review", "finalize"}:
            selected_path = candidate_path.parent / "selected.jsonl"
            for label, path in (
                ("selection", selected_path),
                ("MILP evidence", milp_path),
            ):
                if path.is_symlink() or not path.is_file():
                    raise RoundTransactionError(
                        f"legacy pending round is missing {label}: {path}"
                    )
                try:
                    read_jsonl_range(path, 0)
                except ValueError as exc:
                    raise RoundTransactionError(
                        f"legacy pending round has invalid {label}"
                    ) from exc

        batch_path = self._materialize_legacy_batch(
            number,
            candidate_path.parent,
            candidate_path,
            binding={
                "kind": "pending-pre-transaction-round",
                "phase": phase,
                "candidate_offset": offset,
                "result_checkpoint": checkpoint_binding,
            },
        )
        state["legacy_round_transaction"] = {
            "round": number,
            "candidate_batch": str(batch_path.resolve()),
        }
        self.store.write_state(state)

    @staticmethod
    def _read_validated_candidate_input(path: Path) -> list[dict[str, Any]]:
        try:
            rows, end_offset, _source_sha256 = read_jsonl_range(path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        if end_offset != path.stat().st_size:
            raise RoundTransactionError(
                f"candidate input is not complete bound JSONL: {path}"
            )
        return rows

    def _validated_committed_candidate_history(
        self,
    ) -> tuple[tuple[Path, ...], list[dict[str, Any]]]:
        """Return transaction-replayed candidate inputs and all of their rows.

        ``archive.json`` is only a disposable MAP-Elites cache.  Scheduling
        must instead be rebuilt from the immutable per-round transactions so a
        high BP upper bound cannot permanently hide a runner-up in the same
        archive cell.
        """
        state = self.store.load_state()
        if state is None:
            return (), []
        paths: list[Path] = []
        rows: list[dict[str, Any]] = []
        previous: dict[str, Any] | None = None
        legacy_boundary = False
        seen_v2 = False
        for number in range(1, int(state.get("current_round", 0)) + 1):
            round_dir = self.store.root / "rounds" / f"round-{number:03d}"
            transaction_path = self._transaction_paths(round_dir)["manifest"]
            legacy_sidecar = self._legacy_batch_paths(round_dir)["sidecar"]
            if transaction_path.exists() and legacy_sidecar.exists():
                raise RoundTransactionError(
                    f"round {number} has both legacy and v2 candidate batches"
                )
            if transaction_path.exists():
                transaction, batch_rows = self._validate_completed_transaction(
                    number, round_dir
                )
                start_offset = int(transaction["candidate_start_offset"])
                if previous is None:
                    if not legacy_boundary and start_offset != 0:
                        raise RoundTransactionError(
                            "first pure-v2 transaction must start at candidate offset zero"
                        )
                    if (
                        not legacy_boundary
                        and transaction["mode"] == "openevolve"
                        and transaction.get("base_checkpoint") is not None
                    ):
                        raise RoundTransactionError(
                            "first pure-v2 transaction may not resume an unbound checkpoint"
                        )
                else:
                    if int(previous["candidate_end_offset"]) != start_offset:
                        raise RoundTransactionError(
                            "completed transaction candidate offsets are not contiguous"
                        )
                    if previous.get("result_checkpoint") != transaction.get(
                        "base_checkpoint"
                    ):
                        raise RoundTransactionError(
                            "completed transaction checkpoint chain is broken"
                        )
                if transaction["mode"] == "openevolve":
                    result = transaction["result_checkpoint"]
                    expected_result = (
                        self.evolution_output
                        / "checkpoints"
                        / f"checkpoint_{transaction['expected_result_iteration']}"
                    ).resolve()
                    if Path(result["path"]) != expected_result:
                        raise RoundTransactionError(
                            "completed transaction result checkpoint path is non-canonical"
                        )
                abandoned_inputs = self._abandoned_candidate_inputs(
                    transaction, round_dir
                )
                for path in abandoned_inputs:
                    paths.append(path)
                    rows.extend(self._read_validated_candidate_input(path))
                paths.append(Path(transaction["candidate_batch"]))
                rows.extend(batch_rows)
                previous = transaction
                legacy_boundary = False
                seen_v2 = True
            elif legacy_sidecar.exists():
                if seen_v2:
                    raise RoundTransactionError(
                        "legacy candidate batch may not follow a v2 transaction"
                    )
                path = self._validate_legacy_batch_sidecar(number, round_dir)
                paths.append(path)
                rows.extend(self._read_validated_candidate_input(path))
                previous = None
                legacy_boundary = True
            else:
                raise RoundTransactionError(
                    f"round {number} has no canonical committed candidate batch"
                )
        return tuple(paths), rows

    def _validated_canonical_evaluations(
        self,
        state: dict[str, Any],
    ) -> list[dict[str, Any]]:
        """Strictly replay the canonical Stage 1 audit log for handoff."""
        rows = self._read_canonical_evaluations(
            recover_final_partial=False
        )
        rebuilt = rebuild_audit_state(
            rows,
            fully_exact=is_fully_exact,
            checkpoint_path_for=lambda key: self._milp_checkpoint_path(key),
        )
        recorded_count = state.get("audit_evaluations_seen")
        if (
            recorded_count is not None
            and recorded_count != rebuilt.evaluations_seen
        ):
            raise AuditStateError(
                "canonical evaluation count disagrees with durable state"
            )
        for name, expected in rebuilt.as_state_fields().items():
            recorded = state.get(name)
            if recorded is not None and recorded != expected:
                raise AuditStateError(
                    f"canonical evaluation state disagrees for {name}"
                )
        return rows

    @property
    def pipeline_candidate_inputs(self) -> tuple[Path, ...]:
        state = self.store.load_state()
        if state is None:
            return ()
        candidate_paths, _rows = (
            self._validated_committed_candidate_history()
        )
        paths = list(candidate_paths)
        if self.evaluations_path.exists():
            self._validated_canonical_evaluations(state)
            paths.append(self.evaluations_path.resolve())
        return tuple(paths)

    def _replay_screened_candidate_pool(
        self,
        current: list[dict[str, Any]],
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        """Rebuild the eligible pool from bound history, never archive cache."""
        from evaluation.structural_dedup import deduplicate_css_results

        _paths, historical = self._validated_committed_candidate_history()
        combined = _deduplicate(historical + current)
        combined.sort(key=candidate_fom, reverse=True)
        return deduplicate_css_results(combined)

    def _screen_candidates_with_pool(
        self, rows: list[dict[str, Any]]
    ) -> tuple[
        list[dict[str, Any]],
        list[dict[str, Any]],
        list[dict[str, Any]],
    ]:
        """Apply static and BLISS gates before archive ranking or MILP.

        The persistent archive is regenerated only as an advisory cache.
        Selection separately replays all transaction-bound history, retaining
        same-cell runners-up that MAP-Elites intentionally omits.
        """
        current = _deduplicate(rows)
        current_keys = {code_key(row) for row in current}
        kept, rejected = self._replay_screened_candidate_pool(current)
        self.archive.replace(kept)
        accepted = [row for row in kept if code_key(row) in current_keys]
        return accepted, rejected, kept

    def _screen_candidates(
        self, rows: list[dict[str, Any]]
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        accepted, rejected, _pool = self._screen_candidates_with_pool(rows)
        return accepted, rejected

    def _audit_selected(
        self,
        selected: list[dict[str, Any]],
        *,
        state: dict[str, Any],
        milp_path: Path,
        round_number: int,
    ) -> list[dict[str, Any]]:
        """Audit one ordered selection with a global canonical commit log."""
        global_rows = self._read_canonical_evaluations(
            recover_final_partial=False
        )
        existing = self._reconcile_round_evaluations(
            selected,
            round_number=round_number,
            milp_path=milp_path,
            global_rows=global_rows,
        )
        by_key = {code_key(row): row for row in existing}
        pending = [row for row in selected if code_key(row) not in by_key]
        failures: list[tuple[str, Exception]] = []

        def run_one(
            candidate: dict[str, Any],
        ) -> tuple[dict[str, Any], dict[str, Any]]:
            attempt_config, attempt, invocation = self._attempt_plan(
                candidate,
                state,
                round_number=round_number,
            )
            return (
                self._evaluate_audit_attempt(
                    candidate,
                    attempt_config,
                    invocation,
                ),
                attempt,
            )

        def persist(
            candidate: dict[str, Any],
            result: dict[str, Any],
            attempt: dict[str, Any],
        ) -> None:
            key = code_key(candidate)
            formal_contract = result.pop(
                "_humanize_formal_audit_contract", False
            )
            if not isinstance(formal_contract, bool):
                raise AuditStateError(
                    "internal formal evaluator marker is invalid"
                )
            defining_fields = ("ell", "m", "A_terms", "B_terms")
            provenance_fields = ("static_eligibility", "structural_novelty")
            proposed_identity = dict(result)
            for field in defining_fields:
                if field not in proposed_identity and field in candidate:
                    proposed_identity[field] = candidate[field]
            observed_key = code_key(proposed_identity)
            if observed_key != key:
                raise AuditStateError(
                    "MILP evaluator returned defining fields for a different "
                    f"candidate: expected {key}, got {observed_key}"
                )
            returned_key = result.get("candidate_key")
            if returned_key is not None and returned_key != key:
                raise AuditStateError(
                    "MILP evaluator returned a mismatched candidate_key"
                )
            for field in defining_fields + provenance_fields:
                if field in candidate:
                    result[field] = candidate[field]
                else:
                    result.pop(field, None)
            result["candidate_key"] = key
            result["milp_attempted"] = True
            result["d_is_exact"] = is_fully_exact(result)
            if formal_contract:
                result["audit_attempt"] = seal_audit_attempt_evidence(
                    result,
                    attempt,
                    run_dir=self.run_dir,
                    evidence_root=(
                        self.run_dir / "milp-checkpoints" / "evidence"
                    ),
                )
            else:
                result.pop("audit_evaluator_invocation", None)
                debug_attempt = dict(attempt)
                debug_attempt["schema_version"] = 1
                result["audit_attempt"] = debug_attempt

            # Validate the row and the entire proposed history before changing
            # the canonical log. This rejects non-finite JSON, identity drift,
            # invalid retry metadata, and inconsistent checkpoint history.
            self._canonical_row_identity(result)
            proposed_rows = [*global_rows, result]
            rebuild_audit_state(
                proposed_rows,
                fully_exact=is_fully_exact,
                checkpoint_path_for=lambda candidate_key: (
                    self._milp_checkpoint_path(candidate_key)
                ),
            )

            # The global log is canonical. If the process dies after this
            # rename, the next start reconstructs both state and round output.
            global_rows[:] = proposed_rows
            atomic_write_jsonl(self.evaluations_path, global_rows)
            by_key[key] = result
            atomic_write_jsonl(
                milp_path,
                [
                    by_key[selected_key]
                    for selected_key in (code_key(row) for row in selected)
                    if selected_key in by_key
                ],
            )
            self._rebuild_global_audit_state(
                state,
                recover_final_partial=False,
            )
            state["round_phase"] = "audit"
            self.store.write_state(state)

        if len(pending) == 1:
            candidate = pending[0]
            result, attempt = run_one(candidate)
            persist(candidate, result, attempt)
        elif pending:
            workers = _stage1_milp_worker_count(self.config, len(pending))
            with ThreadPoolExecutor(max_workers=workers) as pool:
                futures = {
                    pool.submit(run_one, candidate): candidate
                    for candidate in pending
                }
                for future in as_completed(futures):
                    candidate = futures[future]
                    try:
                        result, attempt = future.result()
                    except Exception as exc:
                        failures.append((code_key(candidate), exc))
                    else:
                        persist(candidate, result, attempt)

        if failures:
            key, exc = failures[0]
            raise RuntimeError(
                f"MILP audit failed for {key}: {type(exc).__name__}: {exc}"
            ) from exc

        # Reviewer input follows selection order, independent of worker finish
        # order and canonical-log order.
        return [
            by_key[code_key(row)]
            for row in selected
            if code_key(row) in by_key
        ]

    def _write_run_meta(self, state: dict[str, Any]) -> None:
        meta = {
            "run_id": self.store.run_id,
            "status": state["status"],
            "humanize": True,
            "rounds_completed": state["current_round"],
            "total_evaluations": int(state.get("audit_evaluations_seen", 0)),
            "unresolved": len(state.get("unresolved_candidates", {})),
            "best_fom": state.get("best_fom", 0.0),
            "best_exact_fom": state.get("best_exact_fom", 0.0),
            "trusted_exact": int(state.get("trusted_exact_count", 0)),
            "trusted_wins": int(state.get("trusted_win_count", 0)),
            "max_total_workers": self.config.max_total_workers,
            "config": state["config"],
            "state_path": str(self.store.state_path),
            "updated_at": utc_now(),
        }
        path = self.run_dir / "run_meta.json"
        temporary = path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n")
        temporary.replace(path)

    def _write_contract(self, round_number: int, round_dir: Path) -> dict[str, Any]:
        contract = {
            "round": round_number,
            "build": {
                "openevolve_iterations_this_round": self.config.iterations_per_round,
                "openevolve_target_iterations": round_number * self.config.iterations_per_round,
                "model": self.config.model,
                "reasoning_effort": self.config.reasoning_effort,
                "max_total_workers": self.config.max_total_workers,
            },
            "promotion_gates": {
                "static": "commuting, weight/degree <= 6, connected Tanner graph",
                "novelty": "BLISS match plus explicit H_X/H_Z replay",
                "bp_osd": "upper-bound candidate only",
                "milp_top": self.config.milp_top,
                "milp_exact": "all logical directions proven optimal",
                "lean": "performed by archon after search promotion",
            },
            "review": {
                "model": self.config.review_model,
                "reasoning_effort": self.config.review_effort,
                "independent_fresh_session": True,
            },
        }
        (round_dir / "contract.json").write_text(
            json.dumps(contract, ensure_ascii=False, indent=2) + "\n"
        )
        return contract

    def _finish_round(
        self,
        state: dict[str, Any],
        number: int,
        candidates: list[dict[str, Any]],
        audited: list[dict[str, Any]],
        review: dict[str, Any],
        round_dir: Path,
    ) -> None:
        exact = sum(1 for row in audited if row.get("d_is_exact"))
        summary = {
            "round": number,
            "new_candidates": len(candidates),
            "milp_audited": len(audited),
            "milp_exact": exact,
            "best_fom": max((candidate_fom(r) for r in candidates), default=0.0),
            "trusted_exact_total": int(
                state.get("trusted_exact_count", 0)
            ),
            "trusted_win_total": int(state.get("trusted_win_count", 0)),
            "best_exact_fom": float(state.get("best_exact_fom", 0.0)),
            "review_verdict": review["verdict"],
            "review_summary": review["summary"],
        }
        state["rounds"].append(summary)
        state["current_round"] = number
        (round_dir / "summary.md").write_text(
            "\n".join([
                f"# Humanize qcode round {number}", "",
                f"- New candidates: {len(candidates)}",
                f"- MILP audited: {len(audited)}",
                f"- Fully exact MILP: {exact}",
                (
                    "- Trusted exact history: "
                    f"{int(state.get('trusted_exact_count', 0))}"
                ),
                (
                    "- Trusted exact WINs: "
                    f"{int(state.get('trusted_win_count', 0))}"
                ),
                f"- Reviewer verdict: `{review['verdict']}`", "",
                "## Review", "", review["summary"], "",
                "## BitLesson Delta", "",
                f"- Action: {'add' if review['lessons'] else 'none'}",
                f"- Lesson count: {len(review['lessons'])}",
            ]) + "\n"
        )

    def run(
        self,
        *,
        inherited_run_lease: _HumanizeRunLease | None = None,
    ) -> dict[str, Any]:
        # The direct Humanize CLI and candidate-file mode do not necessarily
        # have an outer owner. The five-stage pipeline, however, holds the same
        # lease through Stages 1-5 and passes its exact active lease here so
        # Stage 1 does not deadlock by attempting a second flock.
        if inherited_run_lease is not None:
            _validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            return self._run_with_active_lease()
        with _acquire_humanize_run_lease(self.store):
            return self._run_with_active_lease()

    def _run_with_active_lease(self) -> dict[str, Any]:
        # __init__ may have happened before a previous owner completed. Reload
        # the archive only after this run is known to own (or inherit) its lease.
        self.archive = EliteArchive(self.store.archive_path)
        return self._run_locked()

    def _run_locked(self) -> dict[str, Any]:
        serialized_config = self.config.serializable()
        existing = self.store.load_state()
        if existing is not None:
            durable_config = existing.get("config")
            if durable_config != serialized_config:
                compatible_extension = False
                previous_max_rounds: int | None = None
                requested_max_rounds = serialized_config.get("max_rounds")
                current_round = existing.get("current_round")
                if isinstance(durable_config, dict):
                    previous_max_rounds = durable_config.get("max_rounds")
                    durable_context = dict(durable_config)
                    requested_context = dict(serialized_config)
                    durable_context.pop("max_rounds", None)
                    requested_context.pop("max_rounds", None)
                    compatible_extension = (
                        isinstance(previous_max_rounds, int)
                        and not isinstance(previous_max_rounds, bool)
                        and isinstance(requested_max_rounds, int)
                        and not isinstance(requested_max_rounds, bool)
                        and isinstance(current_round, int)
                        and not isinstance(current_round, bool)
                        and 0 <= current_round <= previous_max_rounds
                        and requested_max_rounds > previous_max_rounds
                        and durable_context == requested_context
                    )
                if not compatible_extension:
                    raise ValueError(
                        "Refusing to resume a Humanize run with different "
                        "configuration"
                    )

                extension_history = existing.get(
                    "config_extension_events", []
                )
                if not isinstance(extension_history, list):
                    raise ValueError(
                        "Refusing to resume a Humanize run with malformed "
                        "configuration extension history"
                    )
                assert previous_max_rounds is not None
                extended_at = utc_now()
                extension_event = {
                    "schema_version": 1,
                    "event": "max_rounds_extended",
                    "sequence": len(extension_history) + 1,
                    "from_max_rounds": previous_max_rounds,
                    "to_max_rounds": requested_max_rounds,
                    "current_round": current_round,
                    "extended_at": extended_at,
                }
                extended = copy.deepcopy(existing)
                extended["config"] = copy.deepcopy(serialized_config)
                extended["config_extension_events"] = [
                    *copy.deepcopy(extension_history),
                    extension_event,
                ]
                # The authoritative config update and its extension event are
                # one atomic state-file transaction. The append-only event log
                # below is an operational mirror of this durable record.
                self.store.write_state(extended)
                self.store.event(
                    "max_rounds_extended",
                    sequence=extension_event["sequence"],
                    from_max_rounds=previous_max_rounds,
                    to_max_rounds=requested_max_rounds,
                    current_round=current_round,
                    extended_at=extended_at,
                )
        state = self.store.initialize(serialized_config)
        state["runtime_worker_budget"] = self.config.max_total_workers
        global_rows, rebuilt = self._rebuild_global_audit_state(
            state,
            recover_final_partial=True,
        )
        trusted_exact, trusted_wins = self._trusted_exact_audit_view(
            global_rows
        )
        self._record_trusted_audit_view(
            state, trusted_exact, trusted_wins
        )
        self.store.write_state(state)
        transaction_version = state.get("round_transaction_version")
        if transaction_version is None:
            self._migrate_legacy_completed_rounds(state)
            if state.get("pending_round") is None:
                state["round_transaction_version"] = (
                    ROUND_TRANSACTION_PROTOCOL_VERSION
                )
                transaction_version = ROUND_TRANSACTION_PROTOCOL_VERSION
                self.store.write_state(state)
        if transaction_version not in (None, ROUND_TRANSACTION_PROTOCOL_VERSION):
            raise RoundTransactionError(
                f"unsupported round transaction version: {transaction_version!r}"
            )
        if trusted_wins and state.get("pending_round") is None:
            already_complete = state.get("status") == "search-complete"
            state["status"] = "search-complete"
            self.store.write_state(state)
            self._write_run_meta(state)
            if not already_complete:
                self.store.event(
                    "search_completed_from_trusted_history",
                    rounds=state["current_round"],
                    trusted_exact=len(trusted_exact),
                    trusted_wins=len(trusted_wins),
                    unresolved_handed_off=len(rebuilt.unresolved),
                )
            return state
        if (
            state["status"] in {"completed", "search-complete"}
            and state.get("pending_round") is None
            and (not rebuilt.unresolved or trusted_wins)
        ):
            self._write_run_meta(state)
            return state

        state.pop("failure", None)
        state["status"] = "running"
        self.store.write_state(state)
        self._write_run_meta(state)

        for number in range(int(state["current_round"]) + 1, self.config.max_rounds + 1):
            round_dir = self.store.round_dir(number)
            contract = self._write_contract(number, round_dir)
            self.store.event("round_started", round_number=number)

            try:
                rejected_path = round_dir / "rejected-candidates.jsonl"
                selected_path = round_dir / "selected.jsonl"
                candidate_path = round_dir / "candidates.jsonl"
                milp_path = round_dir / "milp.jsonl"
                review_path = round_dir / "review.json"
                pending = state.get("pending_round") == number
                phase = state.get("round_phase")
                legacy_pending = (
                    pending
                    and state.get("round_transaction_version") is None
                )
                if state.get("pending_round") not in (None, number):
                    raise RoundTransactionError(
                        "durable state refers to a different pending round"
                    )
                if legacy_pending:
                    self._validate_legacy_pending_round(
                        state, number, candidate_path, milp_path
                    )

                resume_review = pending and phase in {"review", "finalize"}
                if resume_review:
                    if not legacy_pending:
                        self._capture_round_candidates(state, number, round_dir)
                    if (
                        not candidate_path.is_file()
                        or not selected_path.is_file()
                        or not milp_path.is_file()
                    ):
                        raise RoundTransactionError(
                            "review phase is missing candidates, selection, or MILP evidence"
                        )
                    candidates = self._read_jsonl(candidate_path)
                    selected = self._read_jsonl(selected_path)
                    global_rows = self._read_canonical_evaluations(
                        recover_final_partial=False
                    )
                    audited = self._reconcile_round_evaluations(
                        selected,
                        round_number=number,
                        milp_path=milp_path,
                        global_rows=global_rows,
                    )
                    if len(audited) != len(selected):
                        raise RoundTransactionError(
                            "review phase lacks canonical global MILP evidence"
                        )
                    self.store.event(
                        "round_resumed", round_number=number,
                        phase=phase,
                    )
                else:
                    screened_history: list[dict[str, Any]] | None = None
                    if pending and phase not in {"screen", "audit"}:
                        raise RoundTransactionError(
                            f"cannot resume pending round phase {phase!r}"
                        )
                    if legacy_pending:
                        candidates = self._read_jsonl(candidate_path)
                    elif pending:
                        raw_candidates = self._capture_round_candidates(
                            state, number, round_dir
                        )
                        candidates = (
                            raw_candidates
                            if phase == "screen"
                            else self._read_jsonl(candidate_path)
                        )
                    else:
                        candidates = self._capture_round_candidates(
                            state, number, round_dir
                        )

                    if state.get("round_phase") == "screen":
                        (
                            candidates,
                            rejected,
                            screened_history,
                        ) = self._screen_candidates_with_pool(candidates)
                        self._write_jsonl(candidate_path, candidates)
                        self._write_jsonl(rejected_path, rejected)
                    elif state.get("round_phase") == "audit":
                        if not candidate_path.is_file():
                            raise RoundTransactionError(
                                "audit phase is missing screened candidates"
                            )
                        candidates = self._read_jsonl(candidate_path)
                    else:
                        raise RoundTransactionError(
                            "round transaction did not reach screen/audit"
                        )

                    if selected_path.is_file():
                        selected = self._read_jsonl(selected_path)
                    elif state.get("round_phase") == "screen":
                        selected = self._select_audit_candidates(
                            candidates,
                            state,
                            screened_history=screened_history,
                        )
                        self._write_jsonl(selected_path, selected)
                    else:
                        raise RoundTransactionError(
                            "audit phase is missing the durable selection"
                        )
                    if not milp_path.exists():
                        self._write_jsonl(milp_path, [])
                    state["pending_round"] = number
                    state["round_phase"] = "audit"
                    self.store.write_state(state)
                    self.store.event(
                        "round_resumed" if pending else "round_batch_committed",
                        round_number=number,
                        phase="audit",
                    )
                    audited = self._audit_selected(
                        selected,
                        state=state,
                        milp_path=milp_path,
                        round_number=number,
                    )
                    state["round_phase"] = "review"
                    self.store.write_state(state)

                canonical_rows = self._read_canonical_evaluations(
                    recover_final_partial=False
                )
                trusted_exact, trusted_wins = (
                    self._trusted_exact_audit_view(canonical_rows)
                )
                memory = self.store.memory_path.read_text() if self.store.memory_path.exists() else ""
                prompt = build_review_prompt(
                    round_number=number,
                    contract=contract,
                    candidates=candidates,
                    audited=audited,
                    archive_top=self.archive.ranked(),
                    trusted_exact_history=trusted_exact,
                    trusted_exact_wins=trusted_wins,
                    memory=memory,
                )
                (round_dir / "review-request.md").write_text(prompt)
                if state.get("round_phase") == "finalize" and review_path.is_file():
                    review = validate_review(json.loads(review_path.read_text()))
                else:
                    review = self.reviewer.review(prompt, round_dir)
                    if not review_path.exists():
                        review_path.write_text(json.dumps(review, ensure_ascii=False, indent=2) + "\n")
                    state["round_phase"] = "finalize"
                    self.store.write_state(state)

                if review["verdict"] != "reject_round":
                    self.store.add_lessons(review["lessons"], number)

                round_best = max((candidate_fom(r) for r in candidates), default=0.0)
                previous_best = float(state.get("best_fom", 0.0))
                if round_best > previous_best + self.config.min_improvement:
                    state["best_fom"] = round_best
                    state["no_improvement_rounds"] = 0
                else:
                    state["no_improvement_rounds"] = int(
                        state.get("no_improvement_rounds", 0)
                    ) + 1

                self._record_trusted_audit_view(
                    state, trusted_exact, trusted_wins
                )
                self._finish_round(state, number, candidates, audited, review, round_dir)
                unresolved_count = len(
                    state.get("unresolved_candidates", {})
                )
                # Search termination is a machine decision.  Reviewer advice
                # and BP-based patience can never stop a no-WIN run.  A
                # formally replayed exact WIN, however, is enough to hand off
                # immediately even if unrelated candidates remain unresolved.
                should_stop = bool(trusted_wins)
                self.store.event(
                    "round_completed",
                    round_number=number,
                    reviewer_verdict=review["verdict"],
                    exact_total=len(trusted_exact),
                    trusted_win_total=len(trusted_wins),
                    unresolved=unresolved_count,
                    stop=should_stop,
                )
                state["round_transaction_version"] = (
                    ROUND_TRANSACTION_PROTOCOL_VERSION
                )
                state.pop("pending_round", None)
                state.pop("round_phase", None)
                state.pop("legacy_round_transaction", None)
                self.store.write_state(state)
                self._write_run_meta(state)
                if should_stop:
                    break
            except (Exception, KeyboardInterrupt) as exc:
                state["status"] = "failed"
                state["failure"] = f"{type(exc).__name__}: {exc}"
                self.store.write_state(state)
                self._write_run_meta(state)
                self.store.event(
                    "round_failed", round_number=number, error=state["failure"]
                )
                raise

        canonical_rows = self._read_canonical_evaluations(
            recover_final_partial=False
        )
        trusted_exact, trusted_wins = self._trusted_exact_audit_view(
            canonical_rows
        )
        self._record_trusted_audit_view(
            state, trusted_exact, trusted_wins
        )
        unresolved_count = len(state.get("unresolved_candidates", {}))
        if unresolved_count and not trusted_wins:
            state["status"] = "incomplete-unresolved"
            self.store.write_state(state)
            self._write_run_meta(state)
            self.store.event(
                "search_incomplete_unresolved",
                rounds=state["current_round"],
                unresolved=unresolved_count,
            )
            raise UnresolvedAuditError(
                "Stage 1 exhausted max_rounds with "
                f"{unresolved_count} unresolved MILP candidate(s)"
            )

        state["status"] = "search-complete"
        self.store.write_state(state)
        self._write_run_meta(state)
        self.store.event(
            "search_completed",
            rounds=state["current_round"],
            trusted_exact=len(trusted_exact),
            trusted_wins=len(trusted_wins),
            unresolved_handed_off=unresolved_count,
        )
        return state
