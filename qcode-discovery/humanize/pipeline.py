"""Deterministic, resumable orchestration for the qcode five-stage campaign.

The controller deliberately keeps mathematical routing separate from Humanize
reviews.  Reviews are mandatory by default, but are advisory: only machine
artifacts decide whether a candidate advances to a certificate or the strict
terminal gate.
"""

from __future__ import annotations

import fcntl
import hashlib
import importlib.util
import inspect
import json
import marshal
import math
import os
import re
import stat
import subprocess
import sys
import tempfile
import threading
import time
import types
import uuid
from contextlib import ExitStack, contextmanager
from dataclasses import dataclass, field, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, Protocol, Sequence

from evaluation.proof_runtime import (
    RuntimeProbeError,
    probe_python_runtime,
    proof_runtime_fingerprint,
    validate_proof_runtime_fingerprint,
)

from .flow import (
    FlowConfig,
    HumanizeFlow,
    HumanizeRunAlreadyActiveError,
    RoundTransactionError,
    UnresolvedAuditError,
    _HumanizeRunLease,
    _acquire_humanize_run_lease,
)
from .reviewer import CodexReviewer, validate_review
from .state import RunStore

PIPELINE_SCHEMA_VERSION = 1
REVIEW_PROMPT_VERSION = 1
STAGE2_SELECTION_LEDGER_SCHEMA_VERSION = 1
STAGE2_SELECTION_LEDGER_GATE = "qldpc-stage2-selection-ledger"
PROOF_RETRY_CONTROLLER_SCHEMA_VERSION = 1
PROOF_RETRY_CONTROLLER_GATE = "qldpc-proof-retry-controller"
MAX_AUTOMATIC_PROOF_PASSES = 64
RECOVERABLE_PROOF_EXIT_CODES = frozenset({2})
STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES = frozenset(
    {
        "STAGE2_CANONICALIZATION_ERRORS",
        "STAGE2_MALFORMED_RECORDS",
        "STAGE2_UNSUPPORTED_CANDIDATES_SKIPPED",
    }
)
STAGE_ORDER = (
    "stage1_search",
    "stage2_sector_audit",
    "stage3_direction_audit",
    "stage4_certificate_merge",
    "stage5_strict_gate",
)
TERMINAL_STATUSES = {"COMPLETED_WIN", "COMPLETED_NO_WIN"}
REQUIRED_STRICT_REPLAY_CHECKS = frozenset(
    {
        "schema",
        "certificate_sha256",
        "known_answer_sha256",
        "matrix_sha256",
        "direction_count",
        "stored_direction_evidence",
        "milp_rerun",
        "distance_recomputed",
        "final_gate",
        "certificate_passed_flag",
    }
)
_PYCACHE_ENVIRONMENT_LOCK = threading.RLock()


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        default=str,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _audit_json_sha256(value: Mapping[str, Any]) -> str:
    """Match the durable payload hash written by audit_candidate_pool.py."""

    encoded = json.dumps(
        dict(value),
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _certificate_sha256(value: Mapping[str, Any]) -> str:
    """Recompute the self hash shared by all supported certificate types."""

    unsigned = dict(value)
    unsigned.pop("certificate_sha256", None)
    encoded = json.dumps(
        unsigned,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(
        os, "O_NOFOLLOW", 0
    )
    descriptor = os.open(path, flags)
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise OSError(f"not a regular file: {path}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            while chunk := stream.read(1024 * 1024):
                digest.update(chunk)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    return digest.hexdigest()


def _source_file_identity(path: Path) -> dict[str, Any]:
    """Hash one source while binding metadata that detects restore-after-use."""

    digest = hashlib.sha256()
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(
        os, "O_NOFOLLOW", 0
    )
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise OSError(f"not a regular file: {path}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            while chunk := stream.read(1024 * 1024):
                digest.update(chunk)
            after = os.fstat(stream.fileno())
        fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns")
        if any(getattr(before, name) != getattr(after, name) for name in fields):
            raise OSError(f"source changed while it was being hashed: {path}")
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    return {
        "sha256": digest.hexdigest(),
        "bytes": int(after.st_size),
        "mode": stat.S_IMODE(after.st_mode),
        "device": int(after.st_dev),
        "inode": int(after.st_ino),
        "mtime_ns": int(after.st_mtime_ns),
        "ctime_ns": int(after.st_ctime_ns),
    }


def _lexical_absolute(path: str | os.PathLike[str] | Path) -> Path:
    """Return an absolute path without resolving any symlink."""

    return Path(os.path.abspath(os.fspath(path)))


_UNTRUSTED_IMPORT_ARTIFACT_SUFFIXES = (
    ".so",
    ".pyd",
    ".dll",
    ".dylib",
    ".pyc",
    ".pyo",
)


def _is_untrusted_import_artifact(path: Path) -> bool:
    """Return whether an unhashed file could supply executable Python code."""

    name = path.name.lower()
    if name.endswith(".pyc") and path.parent.name == "__pycache__":
        source = _source_for_pep3147_cache(path)
        if source is not None:
            try:
                metadata = source.lstat()
            except OSError:
                pass
            else:
                if (
                    stat.S_ISREG(metadata.st_mode)
                    and _pyc_matches_current_source(path, source)
                ):
                    return False
    return any(name.endswith(suffix) for suffix in _UNTRUSTED_IMPORT_ARTIFACT_SUFFIXES)


def _normalise_code_object(value: types.CodeType) -> types.CodeType:
    constants = tuple(
        _normalise_code_object(item)
        if isinstance(item, types.CodeType)
        else item
        for item in value.co_consts
    )
    return value.replace(co_consts=constants, co_filename="<qcode-source>")


def _source_for_pep3147_cache(cache: Path) -> Path | None:
    """Return the lexical source path for one ``__pycache__`` artifact."""

    try:
        return Path(importlib.util.source_from_cache(str(cache)))
    except ValueError:
        # ``source_from_cache`` rejects a valid cache for a dotted source name
        # such as ``foo.bar.py``.  Parse only the PEP 3147 shape as a fallback.
        name = cache.name
        if cache.parent.name != "__pycache__" or not name.lower().endswith(
            ".pyc"
        ):
            return None
        body = name[:-4]
        body = re.sub(r"\.opt-[0-9]+$", "", body, flags=re.IGNORECASE)
        stem, separator, cache_tag = body.rpartition(".")
        if not separator or not stem or not cache_tag:
            return None
        return cache.parent.parent / f"{stem}.py"


def _pep3147_cache_tag(cache: Path) -> str | None:
    name = cache.name
    if cache.parent.name != "__pycache__" or not name.lower().endswith(".pyc"):
        return None
    body = re.sub(
        r"\.opt-[0-9]+$",
        "",
        name[:-4],
        flags=re.IGNORECASE,
    )
    _stem, separator, cache_tag = body.rpartition(".")
    return cache_tag if separator and cache_tag else None


def _read_regular_nofollow(path: Path) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(
        os, "O_NOFOLLOW", 0
    )
    descriptor = os.open(path, flags)
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise OSError(f"not a regular file: {path}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _pyc_matches_current_source(cache: Path, source: Path) -> bool:
    """Accept an inert stale cache or bytecode identical to its bound source."""

    try:
        raw = _read_regular_nofollow(cache)
        if len(raw) < 16:
            return False
        if raw[:4] != importlib.util.MAGIC_NUMBER:
            # A cache tagged for another implementation/version is inert for
            # this process. All child execution paths also use a fresh
            # PYTHONPYCACHEPREFIX, so a foreign cache cannot become active.
            current_tag = getattr(sys.implementation, "cache_tag", None)
            return (
                isinstance(current_tag, str)
                and _pep3147_cache_tag(cache) != current_tag
            )
        flags = int.from_bytes(raw[4:8], "little")
        if flags & ~0b11:
            return False
        before = source.lstat()
        if not stat.S_ISREG(before.st_mode):
            return False
        source_bytes = _read_regular_nofollow(source)
        after = source.lstat()
        identity_fields = (
            "st_dev",
            "st_ino",
            "st_mode",
            "st_size",
            "st_mtime_ns",
            "st_ctime_ns",
        )
        if any(
            getattr(before, field) != getattr(after, field)
            for field in identity_fields
        ):
            return False
        if flags == 0:
            cached_mtime = int.from_bytes(raw[8:12], "little")
            cached_size = int.from_bytes(raw[12:16], "little")
            source_mtime = int(after.st_mtime) & 0xFFFFFFFF
            source_size = len(source_bytes) & 0xFFFFFFFF
            if (cached_mtime, cached_size) != (source_mtime, source_size):
                # CPython ignores an out-of-date timestamp cache and recompiles
                # the source, so it cannot override the hashed source file.
                return True
        loaded = marshal.loads(raw[16:])
        if not isinstance(loaded, types.CodeType):
            return False
        optimisation = 0
        match = re.search(r"\.opt-([0-9]+)\.pyc$", cache.name.lower())
        if match is not None:
            optimisation = int(match.group(1))
        compiled = compile(
            source_bytes,
            str(source),
            "exec",
            dont_inherit=True,
            optimize=optimisation,
        )
        return marshal.dumps(_normalise_code_object(loaded)) == marshal.dumps(
            _normalise_code_object(compiled)
        )
    except (
        EOFError,
        OSError,
        OverflowError,
        RecursionError,
        SyntaxError,
        TypeError,
        ValueError,
    ):
        return False


def _reject_symlink_components(
    path: str | os.PathLike[str] | Path,
    *,
    classification: str,
    label: str,
) -> Path:
    """Reject every existing symlink in a lexical absolute path."""

    absolute = _lexical_absolute(path)
    current = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        current /= part
        try:
            metadata = current.lstat()
        except FileNotFoundError:
            continue
        except OSError as exc:
            raise PipelineError(
                classification,
                f"cannot inspect {label} path component {current}: {exc}",
            ) from exc
        if stat.S_ISLNK(metadata.st_mode):
            raise PipelineError(
                classification,
                f"{label} path component may not be a symlink: {current}",
            )
    return absolute


def _hash_paths(
    paths: Iterable[Path],
    *,
    require: bool = True,
    classification: str = "UNSAFE_INPUT_PATH",
    label: str = "input",
) -> dict[str, str | None]:
    result: dict[str, str | None] = {}
    for original in paths:
        path = _reject_symlink_components(
            original,
            classification=classification,
            label=label,
        )
        try:
            metadata = path.lstat()
        except FileNotFoundError:
            if require:
                raise PipelineError(
                    "INPUT_MISSING",
                    f"required file does not exist: {path}",
                )
            result[str(path)] = None
            continue
        except OSError as exc:
            raise PipelineError(
                classification,
                f"cannot inspect {label} file {path}: {exc}",
            ) from exc
        if not stat.S_ISREG(metadata.st_mode):
            raise PipelineError(
                classification,
                f"{label} is not a regular file: {path}",
            )
        try:
            result[str(path)] = _file_sha256(path)
        except OSError as exc:
            raise PipelineError(
                classification,
                f"cannot hash {label} file {path}: {exc}",
            ) from exc
    return result


def _atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        try:
            directory_fd = os.open(path.parent, os.O_RDONLY)
        except OSError:
            directory_fd = None
        if directory_fd is not None:
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    _atomic_write_text(
        path,
        json.dumps(dict(value), ensure_ascii=False, indent=2, default=str) + "\n",
    )


def atomic_write_jsonl(path: Path, rows: Iterable[Mapping[str, Any]]) -> None:
    _atomic_write_text(
        path,
        "".join(
            json.dumps(dict(row), ensure_ascii=False, sort_keys=True, default=str)
            + "\n"
            for row in rows
        ),
    )


def _read_json_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise PipelineError(
            "OUTPUT_INVALID",
            f"cannot read JSON object {path}: {exc}",
        ) from exc
    if not isinstance(value, dict):
        raise PipelineError("OUTPUT_INVALID", f"{path} must contain a JSON object")
    return value


def _resolve_path(value: str | os.PathLike[str] | Path, base: Path) -> Path:
    path = Path(value)
    return _lexical_absolute(base / path if not path.is_absolute() else path)


def _safe_run_id(value: str) -> str:
    original = str(value)
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}", original) or original in {
        ".",
        "..",
    }:
        raise ValueError("run_id must match [A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
    return original


class PipelineError(RuntimeError):
    """A classified, durable pipeline failure."""

    def __init__(
        self,
        classification: str,
        message: str,
        *,
        stage: str | None = None,
        exit_code: int | None = None,
    ):
        super().__init__(message)
        self.classification = classification
        self.stage = stage
        self.exit_code = exit_code


class PipelineBusyError(PipelineError):
    """Another process owns this campaign's execution lock."""


class CommandRunner(Protocol):
    def __call__(
        self,
        command: list[str],
        *,
        cwd: Path,
    ) -> subprocess.CompletedProcess[str]: ...


class StageReviewer(Protocol):
    def review(
        self,
        stage: str,
        prompt: str,
        stage_dir: Path,
    ) -> dict[str, Any]: ...


FlowFactory = Callable[[FlowConfig], Any]


def default_command_runner(
    command: list[str],
    *,
    cwd: Path,
) -> subprocess.CompletedProcess[str]:
    """Run one stage synchronously; stages can never overlap."""

    with tempfile.TemporaryDirectory(prefix="qcode-stage-pycache-") as cache:
        environment = os.environ.copy()
        environment["PYTHONPYCACHEPREFIX"] = cache
        return subprocess.run(
            command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
            env=environment,
        )


@dataclass(frozen=True)
class PipelineConfig:
    """Configuration for one deterministic five-stage qcode campaign."""

    repo_dir: Path
    run_id: str
    candidate_inputs: tuple[Path, ...] = ()
    flow_config: FlowConfig | None = None
    pipeline_dir: Path | None = None
    python_executable: str = sys.executable
    resume: bool = True

    stage2_top: int = 20
    stage2_timeout: float = 300
    stage2_candidate_workers: int = 2
    stage2_solver_workers: int = 4

    stage3_top: int = 0
    stage3_timeout: float = 300
    stage3_candidate_workers: int = 1
    stage3_direction_workers: int = 4
    stage3_exact: bool = False

    certificate_workers: int = 1
    certificate_solver_workers: int = 1
    max_total_workers: int = 8
    certificate_timeout_per_logical: float = 300
    certificate_total_timeout: float = 7200
    verification_timeout_per_logical: float = 300
    verification_total_timeout: float = 7200
    proof_retry_max_attempts: int = 6
    proof_retry_max_multiplier: float = 4
    proof_retry_campaign_total_timeout: float = 86400
    proof_retry_backoff_seconds: float = 2

    known_answer_artifact: Path | None = None
    known_answer_trust: Path | None = None
    known_answer_timeout_per_logical: int = 300
    known_answer_total_timeout: int = 7200

    stage_review: bool = True
    reviewer_model: str = "gpt-5.5"
    reviewer_effort: str = "xhigh"

    def __post_init__(self) -> None:
        repo = Path(self.repo_dir).resolve()
        object.__setattr__(self, "repo_dir", repo)
        object.__setattr__(self, "run_id", _safe_run_id(self.run_id))
        raw_python = self.python_executable
        if (
            not isinstance(raw_python, str)
            or not raw_python
            or "\x00" in raw_python
            or (
                os.path.sep not in raw_python
                and (
                    os.path.altsep is None
                    or os.path.altsep not in raw_python
                )
            )
        ):
            raise ValueError(
                "python_executable must be an explicit path, not a "
                "PATH-resolved command"
            )
        python_path = Path(raw_python)
        if not python_path.is_absolute():
            python_path = repo / python_path
        object.__setattr__(
            self,
            "python_executable",
            str(Path(os.path.abspath(python_path))),
        )
        control_base = _reject_symlink_components(
            repo / "results" / "humanize" / "pipelines",
            classification="UNSAFE_CONTROL_PATH",
            label="pipeline control root",
        )
        try:
            control_base.relative_to(repo)
        except ValueError as exc:
            raise ValueError(
                f"pipeline control root escapes repository: {control_base}"
            ) from exc
        fixed_root = _reject_symlink_components(
            control_base / self.run_id,
            classification="UNSAFE_CONTROL_PATH",
            label="pipeline run root",
        )
        try:
            fixed_root.relative_to(control_base)
        except ValueError as exc:
            raise ValueError(
                f"pipeline state path escapes the fixed control root: {fixed_root}"
            ) from exc
        object.__setattr__(
            self,
            "candidate_inputs",
            tuple(_resolve_path(path, repo) for path in self.candidate_inputs),
        )
        if self.pipeline_dir is not None:
            pipeline_dir = _resolve_path(self.pipeline_dir, repo)
            if pipeline_dir != fixed_root:
                raise ValueError(
                    "pipeline_dir must equal the fixed campaign control root: "
                    f"{fixed_root}"
                )
            object.__setattr__(self, "pipeline_dir", pipeline_dir)
        if self.known_answer_artifact is None:
            object.__setattr__(
                self,
                "known_answer_artifact",
                repo / "results" / "known_answer_gate.json",
            )
        else:
            object.__setattr__(
                self,
                "known_answer_artifact",
                _resolve_path(self.known_answer_artifact, repo),
            )
        if self.known_answer_trust is None:
            object.__setattr__(
                self,
                "known_answer_trust",
                repo / "results" / "known_answer_trust.json",
            )
        else:
            object.__setattr__(
                self,
                "known_answer_trust",
                _resolve_path(self.known_answer_trust, repo),
            )
        if self.flow_config is not None:
            declared_budget = self.flow_config.max_total_workers
            if (
                declared_budget is not None
                and declared_budget != self.max_total_workers
            ):
                raise ValueError(
                    "flow_config.max_total_workers conflicts with the "
                    "pipeline max_total_workers"
                )
            object.__setattr__(
                self,
                "flow_config",
                replace(
                    self.flow_config,
                    max_total_workers=self.max_total_workers,
                ),
            )
        self.validate()

    @property
    def root(self) -> Path:
        return self.pipeline_dir or (
            self.repo_dir / "results" / "humanize" / "pipelines" / self.run_id
        )

    def validate(self) -> None:
        if (
            isinstance(self.stage2_top, bool)
            or not isinstance(self.stage2_top, int)
            or self.stage2_top < 1
        ):
            raise ValueError(
                "stage2_top must be a positive integer so every proof page "
                "can advance"
            )
        if (
            isinstance(self.stage3_top, bool)
            or not isinstance(self.stage3_top, int)
            or self.stage3_top != 0
        ):
            raise ValueError(
                "stage3_top must be 0: Stage 3 must audit every unresolved "
                "candidate in the bounded current Stage 2 page"
            )
        positive_numbers = {
            "stage2_timeout": self.stage2_timeout,
            "stage3_timeout": self.stage3_timeout,
            "certificate_timeout_per_logical": self.certificate_timeout_per_logical,
            "certificate_total_timeout": self.certificate_total_timeout,
            "verification_timeout_per_logical": self.verification_timeout_per_logical,
            "verification_total_timeout": self.verification_total_timeout,
            "proof_retry_max_multiplier": self.proof_retry_max_multiplier,
            "proof_retry_campaign_total_timeout": (
                self.proof_retry_campaign_total_timeout
            ),
            "known_answer_timeout_per_logical": self.known_answer_timeout_per_logical,
            "known_answer_total_timeout": self.known_answer_total_timeout,
        }
        for name, value in positive_numbers.items():
            if isinstance(value, bool) or not math.isfinite(float(value)) or value <= 0:
                raise ValueError(f"{name} must be positive and finite")
        worker_values = {
            "stage2_candidate_workers": self.stage2_candidate_workers,
            "stage2_solver_workers": self.stage2_solver_workers,
            "stage3_candidate_workers": self.stage3_candidate_workers,
            "stage3_direction_workers": self.stage3_direction_workers,
            "certificate_workers": self.certificate_workers,
            "certificate_solver_workers": self.certificate_solver_workers,
            "max_total_workers": self.max_total_workers,
            "proof_retry_max_attempts": self.proof_retry_max_attempts,
        }
        for name, value in worker_values.items():
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise ValueError(f"{name} must be a positive integer")
        if (
            isinstance(self.proof_retry_backoff_seconds, bool)
            or not math.isfinite(float(self.proof_retry_backoff_seconds))
            or self.proof_retry_backoff_seconds < 0
        ):
            raise ValueError(
                "proof_retry_backoff_seconds must be finite and non-negative"
            )
        if self.proof_retry_max_multiplier < 1:
            raise ValueError("proof_retry_max_multiplier must be at least 1")
        if self.certificate_solver_workers > 8:
            raise ValueError("certificate_solver_workers must be between 1 and 8")
        for candidates, solvers, label in (
            (
                self.stage2_candidate_workers,
                self.stage2_solver_workers,
                "Stage 2",
            ),
            (
                self.stage3_candidate_workers,
                self.stage3_direction_workers,
                "Stage 3",
            ),
            (
                self.certificate_workers,
                self.certificate_solver_workers,
                "certificate",
            ),
        ):
            if candidates * solvers > self.max_total_workers:
                raise ValueError(
                    f"{label} workers exceed max_total_workers: "
                    f"{candidates} * {solvers} > {self.max_total_workers}"
                )
        if self.candidate_inputs and self.flow_config is not None:
            raise ValueError(
                "candidate_inputs and flow_config are mutually exclusive Stage 1 sources"
            )
        if self.flow_config is not None:
            if self.flow_config.repo_dir.resolve() != self.repo_dir:
                raise ValueError("flow_config.repo_dir must equal repo_dir")
            if self.flow_config.run_id != self.run_id:
                raise ValueError("flow_config.run_id must equal run_id")

    def serializable(self) -> dict[str, Any]:
        return {
            "repo_dir": str(self.repo_dir),
            "run_id": self.run_id,
            "candidate_inputs": [str(path) for path in self.candidate_inputs],
            "flow_config": (
                None if self.flow_config is None else self.flow_config.serializable()
            ),
            "pipeline_dir": str(self.pipeline_dir) if self.pipeline_dir else None,
            "python_executable": self.python_executable,
            "resume": self.resume,
            "stage2_top": self.stage2_top,
            "stage2_timeout": self.stage2_timeout,
            "stage2_candidate_workers": self.stage2_candidate_workers,
            "stage2_solver_workers": self.stage2_solver_workers,
            "stage3_top": self.stage3_top,
            "stage3_timeout": self.stage3_timeout,
            "stage3_candidate_workers": self.stage3_candidate_workers,
            "stage3_direction_workers": self.stage3_direction_workers,
            "stage3_exact": self.stage3_exact,
            "certificate_workers": self.certificate_workers,
            "certificate_solver_workers": self.certificate_solver_workers,
            "max_total_workers": self.max_total_workers,
            "certificate_timeout_per_logical": self.certificate_timeout_per_logical,
            "certificate_total_timeout": self.certificate_total_timeout,
            "verification_timeout_per_logical": self.verification_timeout_per_logical,
            "verification_total_timeout": self.verification_total_timeout,
            "proof_retry_max_attempts": self.proof_retry_max_attempts,
            "proof_retry_max_multiplier": self.proof_retry_max_multiplier,
            "proof_retry_campaign_total_timeout": (
                self.proof_retry_campaign_total_timeout
            ),
            "proof_retry_backoff_seconds": self.proof_retry_backoff_seconds,
            "known_answer_artifact": str(self.known_answer_artifact),
            "known_answer_trust": str(self.known_answer_trust),
            "known_answer_timeout_per_logical": (self.known_answer_timeout_per_logical),
            "known_answer_total_timeout": self.known_answer_total_timeout,
            "stage_review": self.stage_review,
            "reviewer_model": self.reviewer_model,
            "reviewer_effort": self.reviewer_effort,
        }

    @classmethod
    def from_json(
        cls,
        path: Path,
        *,
        repo_dir: Path,
        run_id: str | None = None,
        stage_review: bool | None = None,
        reviewer_model: str | None = None,
        reviewer_effort: str | None = None,
    ) -> "PipelineConfig":
        """Load a JSON config, accepting flat fields or stage subsections."""

        config_path = Path(path)
        value = json.loads(config_path.read_text())
        if not isinstance(value, dict):
            raise ValueError("pipeline config must be a JSON object")
        base = Path(repo_dir).resolve()
        selected_run_id = run_id or value.get("run_id")
        if not selected_run_id:
            raise ValueError("run_id is required in JSON or as an override")

        def section(name: str) -> dict[str, Any]:
            nested = value.get(name, {})
            if nested is None:
                return {}
            if not isinstance(nested, dict):
                raise ValueError(f"{name} config must be an object")
            return dict(nested)

        def pick(flat: str, group: str, nested: str, default: Any) -> Any:
            return value.get(flat, section(group).get(nested, default))

        def parse_int(name: str, raw: Any) -> int:
            # bool is an int subclass, so converting first would turn a JSON
            # true/false into a valid-looking 1/0 before validate() can reject it.
            if isinstance(raw, bool):
                raise ValueError(f"{name} must not be boolean")
            return int(raw)

        def parse_float(name: str, raw: Any) -> float:
            if isinstance(raw, bool):
                raise ValueError(f"{name} must not be boolean")
            return float(raw)

        raw_inputs = value.get("candidate_inputs", value.get("stage1_inputs", ()))
        if isinstance(raw_inputs, (str, os.PathLike)):
            raw_inputs = [raw_inputs]
        candidate_inputs = tuple(_resolve_path(item, base) for item in raw_inputs)

        flow_section = value.get("flow_config", value.get("stage1"))
        flow_config: FlowConfig | None = None
        if not candidate_inputs:
            if not isinstance(flow_section, (dict, type(None))):
                raise ValueError("flow_config/stage1 must be an object")
            flow_values = dict(flow_section or {})
            flow_path_fields = ("evolution_config", "evolution_seed", "candidate_file")
            for name in flow_path_fields:
                if flow_values.get(name) is not None:
                    flow_values[name] = _resolve_path(flow_values[name], base)
            allowed = set(FlowConfig.__dataclass_fields__) - {"repo_dir", "run_id"}
            unknown = set(flow_values) - allowed
            if unknown:
                raise ValueError(
                    "unknown flow_config fields: " + ", ".join(sorted(unknown))
                )
            flow_values.setdefault(
                "review_model",
                reviewer_model or value.get("reviewer_model", "gpt-5.5"),
            )
            flow_values.setdefault(
                "review_effort",
                reviewer_effort or value.get("reviewer_effort", "xhigh"),
            )
            flow_config = FlowConfig(
                repo_dir=base,
                run_id=_safe_run_id(str(selected_run_id)),
                **flow_values,
            )

        path_value = value.get("pipeline_dir")
        known_artifact = value.get("known_answer_artifact")
        known_trust = value.get("known_answer_trust")
        review = section("review")
        return cls(
            repo_dir=base,
            run_id=str(selected_run_id),
            candidate_inputs=candidate_inputs,
            flow_config=flow_config,
            pipeline_dir=(
                None if path_value is None else _resolve_path(path_value, base)
            ),
            python_executable=str(value.get("python_executable", sys.executable)),
            resume=bool(value.get("resume", True)),
            stage2_top=parse_int(
                "stage2_top", pick("stage2_top", "stage2", "top", 20)
            ),
            stage2_timeout=parse_float(
                "stage2_timeout", pick("stage2_timeout", "stage2", "timeout", 300)
            ),
            stage2_candidate_workers=parse_int(
                "stage2_candidate_workers",
                pick("stage2_candidate_workers", "stage2", "candidate_workers", 2)
            ),
            stage2_solver_workers=parse_int(
                "stage2_solver_workers",
                pick("stage2_solver_workers", "stage2", "solver_workers", 4)
            ),
            stage3_top=parse_int(
                "stage3_top", pick("stage3_top", "stage3", "top", 0)
            ),
            stage3_timeout=parse_float(
                "stage3_timeout", pick("stage3_timeout", "stage3", "timeout", 300)
            ),
            stage3_candidate_workers=parse_int(
                "stage3_candidate_workers",
                pick("stage3_candidate_workers", "stage3", "candidate_workers", 1)
            ),
            stage3_direction_workers=parse_int(
                "stage3_direction_workers",
                pick("stage3_direction_workers", "stage3", "direction_workers", 4)
            ),
            stage3_exact=bool(pick("stage3_exact", "stage3", "exact", False)),
            certificate_workers=parse_int(
                "certificate_workers",
                pick("certificate_workers", "certificate", "workers", 1)
            ),
            certificate_solver_workers=parse_int(
                "certificate_solver_workers",
                pick(
                    "certificate_solver_workers",
                    "certificate",
                    "solver_workers",
                    1,
                )
            ),
            max_total_workers=parse_int(
                "max_total_workers", value.get("max_total_workers", 8)
            ),
            certificate_timeout_per_logical=parse_float(
                "certificate_timeout_per_logical",
                pick(
                    "certificate_timeout_per_logical",
                    "certificate",
                    "timeout_per_logical",
                    300,
                )
            ),
            certificate_total_timeout=parse_float(
                "certificate_total_timeout",
                pick(
                    "certificate_total_timeout",
                    "certificate",
                    "total_timeout",
                    7200,
                )
            ),
            verification_timeout_per_logical=parse_float(
                "verification_timeout_per_logical",
                pick(
                    "verification_timeout_per_logical",
                    "certificate",
                    "verification_timeout_per_logical",
                    300,
                )
            ),
            verification_total_timeout=parse_float(
                "verification_total_timeout",
                pick(
                    "verification_total_timeout",
                    "certificate",
                    "verification_total_timeout",
                    7200,
                )
            ),
            proof_retry_max_attempts=parse_int(
                "proof_retry_max_attempts",
                pick(
                    "proof_retry_max_attempts",
                    "proof_retry",
                    "max_attempts",
                    6,
                )
            ),
            proof_retry_max_multiplier=parse_float(
                "proof_retry_max_multiplier",
                pick(
                    "proof_retry_max_multiplier",
                    "proof_retry",
                    "max_multiplier",
                    4,
                )
            ),
            proof_retry_campaign_total_timeout=parse_float(
                "proof_retry_campaign_total_timeout",
                pick(
                    "proof_retry_campaign_total_timeout",
                    "proof_retry",
                    "campaign_total_timeout",
                    86400,
                )
            ),
            proof_retry_backoff_seconds=parse_float(
                "proof_retry_backoff_seconds",
                pick(
                    "proof_retry_backoff_seconds",
                    "proof_retry",
                    "backoff_seconds",
                    2,
                )
            ),
            known_answer_artifact=(
                None if known_artifact is None else _resolve_path(known_artifact, base)
            ),
            known_answer_trust=(
                None if known_trust is None else _resolve_path(known_trust, base)
            ),
            known_answer_timeout_per_logical=parse_int(
                "known_answer_timeout_per_logical",
                pick(
                    "known_answer_timeout_per_logical",
                    "strict",
                    "timeout_per_logical",
                    300,
                )
            ),
            known_answer_total_timeout=parse_int(
                "known_answer_total_timeout",
                pick(
                    "known_answer_total_timeout",
                    "strict",
                    "total_timeout",
                    7200,
                )
            ),
            stage_review=(
                bool(stage_review)
                if stage_review is not None
                else bool(value.get("stage_review", review.get("enabled", True)))
            ),
            reviewer_model=(
                reviewer_model
                or value.get("reviewer_model")
                or review.get("model")
                or "gpt-5.5"
            ),
            reviewer_effort=(
                reviewer_effort
                or value.get("reviewer_effort")
                or review.get("effort")
                or "xhigh"
            ),
        )


@dataclass(frozen=True)
class PipelinePaths:
    root: Path
    state: Path = field(init=False)
    artifacts: Path = field(init=False)
    logs: Path = field(init=False)
    reviews: Path = field(init=False)
    solver_state: Path = field(init=False)
    stage2_ranked: Path = field(init=False)
    stage2_summary: Path = field(init=False)
    stage2_selection_ledger: Path = field(init=False)
    proof_retry_controller: Path = field(init=False)
    stage3_ranked: Path = field(init=False)
    stage3_summary: Path = field(init=False)
    stage3_thresholds: Path = field(init=False)
    stage4_certificates: Path = field(init=False)
    stage4_summary: Path = field(init=False)
    stage5_gate: Path = field(init=False)
    stage5_no_win: Path = field(init=False)
    stage5_incomplete: Path = field(init=False)

    def __post_init__(self) -> None:
        root = _lexical_absolute(self.root)
        object.__setattr__(self, "root", root)
        object.__setattr__(self, "state", root / "state.json")
        object.__setattr__(self, "artifacts", root / "artifacts")
        object.__setattr__(self, "logs", root / "logs")
        object.__setattr__(self, "reviews", root / "reviews")
        object.__setattr__(self, "solver_state", root / "solver-state")
        object.__setattr__(
            self, "stage2_ranked", root / "artifacts" / "stage2-ranked.jsonl"
        )
        object.__setattr__(
            self, "stage2_summary", root / "artifacts" / "stage2-summary.json"
        )
        object.__setattr__(
            self,
            "stage2_selection_ledger",
            root / "solver-state" / "stage2-selection-ledger.json",
        )
        object.__setattr__(
            self,
            "proof_retry_controller",
            root / "solver-state" / "proof-retry-controller.json",
        )
        object.__setattr__(
            self, "stage3_ranked", root / "artifacts" / "stage3-ranked.jsonl"
        )
        object.__setattr__(
            self, "stage3_summary", root / "artifacts" / "stage3-summary.json"
        )
        object.__setattr__(
            self,
            "stage3_thresholds",
            root / "artifacts" / "stage3-thresholds.jsonl",
        )
        object.__setattr__(
            self,
            "stage4_certificates",
            root / "artifacts" / "stage4-certificates.jsonl",
        )
        object.__setattr__(
            self, "stage4_summary", root / "artifacts" / "stage4-summary.json"
        )
        object.__setattr__(
            self, "stage5_gate", root / "artifacts" / "stage5-final-gate.json"
        )
        object.__setattr__(
            self, "stage5_no_win", root / "artifacts" / "stage5-no-win.json"
        )
        object.__setattr__(
            self,
            "stage5_incomplete",
            root / "artifacts" / "stage5-incomplete.json",
        )


class FiveStagePipeline:
    """Sequential state machine for search, proof audits, and strict release."""

    def __init__(
        self,
        config: PipelineConfig,
        *,
        command_runner: CommandRunner = default_command_runner,
        flow_factory: FlowFactory = HumanizeFlow,
        reviewer: StageReviewer | Callable[..., dict[str, Any]] | None = None,
        sleeper: Callable[[float], None] = time.sleep,
        monotonic: Callable[[], float] = time.monotonic,
    ):
        self.config = config
        self.paths = PipelinePaths(config.root)
        self.command_runner = command_runner
        self.flow_factory = flow_factory
        self.reviewer = reviewer
        self._sleeper = sleeper
        self._monotonic = monotonic
        self._proof_budget_multiplier = 1.0
        self._humanize_run_lease: _HumanizeRunLease | None = None
        if self.reviewer is None and config.stage_review:
            self.reviewer = CodexReviewer(
                repo_dir=config.repo_dir,
                model=config.reviewer_model,
                effort=config.reviewer_effort,
            )
        self.state: dict[str, Any] = {}

    @property
    def state_path(self) -> Path:
        return self.paths.state

    def _ensure_pipeline_directories(self) -> None:
        """Create fixed run subdirectories without following symlink escapes."""

        root = _reject_symlink_components(
            self.paths.root,
            classification="UNSAFE_CONTROL_PATH",
            label="pipeline run root",
        )
        try:
            root_metadata = root.lstat()
        except OSError as exc:
            raise PipelineError(
                "UNSAFE_CONTROL_PATH",
                f"pipeline run root is unavailable: {root}: {exc}",
            ) from exc
        if not stat.S_ISDIR(root_metadata.st_mode):
            raise PipelineError(
                "UNSAFE_CONTROL_PATH",
                f"pipeline run root is not a directory: {root}",
            )
        for path in (
            self.paths.artifacts,
            self.paths.logs,
            self.paths.reviews,
            self.paths.solver_state,
        ):
            _reject_symlink_components(
                path,
                classification="UNSAFE_CONTROL_PATH",
                label="pipeline directory",
            )
            path.mkdir(mode=0o700, exist_ok=True)
            safe_path = _reject_symlink_components(
                path,
                classification="UNSAFE_CONTROL_PATH",
                label="pipeline directory",
            )
            try:
                metadata = safe_path.lstat()
            except OSError as exc:
                raise PipelineError(
                    "UNSAFE_CONTROL_PATH",
                    f"pipeline directory is unavailable: {safe_path}: {exc}",
                ) from exc
            if not stat.S_ISDIR(metadata.st_mode):
                raise PipelineError(
                    "UNSAFE_CONTROL_PATH",
                    f"pipeline control path is not a directory: {safe_path}",
                )
        self._ensure_solver_state_tree_safe()

    def _ensure_solver_state_tree_safe(self) -> None:
        """Reject links and special files anywhere under solver-owned state."""

        root = self.paths.solver_state.resolve(strict=True)
        pending = [root]
        while pending:
            directory = pending.pop()
            try:
                with os.scandir(directory) as iterator:
                    entries = list(iterator)
            except OSError as exc:
                raise PipelineError(
                    "UNSAFE_CONTROL_PATH",
                    f"cannot inspect solver state directory: {directory}: {exc}",
                ) from exc
            for entry in entries:
                path = Path(entry.path)
                try:
                    metadata = entry.stat(follow_symlinks=False)
                except OSError as exc:
                    raise PipelineError(
                        "UNSAFE_CONTROL_PATH",
                        f"cannot inspect solver state entry: {path}: {exc}",
                    ) from exc
                if stat.S_ISLNK(metadata.st_mode):
                    raise PipelineError(
                        "UNSAFE_CONTROL_PATH",
                        f"solver state entry may not be a symlink: {path}",
                    )
                if stat.S_ISDIR(metadata.st_mode):
                    try:
                        path.resolve(strict=True).relative_to(root)
                    except (OSError, ValueError) as exc:
                        raise PipelineError(
                            "UNSAFE_CONTROL_PATH",
                            f"solver state directory escapes its root: {path}",
                        ) from exc
                    pending.append(path)
                    continue
                if not stat.S_ISREG(metadata.st_mode):
                    raise PipelineError(
                        "UNSAFE_CONTROL_PATH",
                        f"solver state entry must be a regular file: {path}",
                    )

    def _write_state(self) -> None:
        self.state["updated_at"] = utc_now()
        atomic_write_json(self.paths.state, self.state)

    def _load_or_initialize_state(self) -> dict[str, Any]:
        self._ensure_pipeline_directories()
        if self.paths.state.is_file():
            state = _read_json_object(self.paths.state)
            if state.get("schema_version") != PIPELINE_SCHEMA_VERSION:
                raise ValueError(
                    f"unsupported pipeline state schema: {state.get('schema_version')}"
                )
            if state.get("run_id") != self.config.run_id:
                raise ValueError("pipeline state run_id does not match configuration")
        else:
            state = {
                "schema_version": PIPELINE_SCHEMA_VERSION,
                "gate": "qcode-humanize-five-stage-pipeline",
                "run_id": self.config.run_id,
                "status": "PENDING",
                "created_at": utc_now(),
                "updated_at": utc_now(),
                "active_stage": None,
                "config": self.config.serializable(),
                "config_fingerprint": _canonical_sha256(self.config.serializable()),
                "config_history": [],
                "stages": {
                    name: {
                        "ordinal": index,
                        "status": "PENDING",
                        "machine_status": "PENDING",
                        "attempt": 0,
                        "review_status": "PENDING",
                        "review_attempt": 0,
                    }
                    for index, name in enumerate(STAGE_ORDER, start=1)
                },
            }
        current_config = self.config.serializable()
        current_fingerprint = _canonical_sha256(current_config)
        old_fingerprint = state.get("config_fingerprint")
        if old_fingerprint and old_fingerprint != current_fingerprint:
            state.setdefault("config_history", []).append(
                {
                    "changed_at": utc_now(),
                    "fingerprint": old_fingerprint,
                    "config": state.get("config"),
                }
            )
        state["config"] = current_config
        state["config_fingerprint"] = current_fingerprint
        self.state = state
        self._enforce_stage1_identity()
        self._write_state()
        return state

    def _stage1_identity(self) -> dict[str, Any]:
        if self.config.candidate_inputs:
            return {
                "mode": "existing-inputs",
                "paths": [str(path) for path in self.config.candidate_inputs],
                "hashes": _hash_paths(self.config.candidate_inputs),
            }
        flow = self._flow_config()
        return {"mode": "humanize-flow", "flow_config": flow.serializable()}

    def _enforce_stage1_identity(self) -> None:
        current = _canonical_sha256(self._stage1_identity())
        recorded = self.state.get("stage1_identity_fingerprint")
        if recorded is not None and recorded != current:
            raise ValueError(
                "Stage 1 search identity or candidate input changed; use a new run_id"
            )
        self.state["stage1_identity_fingerprint"] = current

    def _flow_config(self) -> FlowConfig:
        if self.config.flow_config is not None:
            return self.config.flow_config
        return FlowConfig(
            repo_dir=self.config.repo_dir,
            run_id=self.config.run_id,
            review_model=self.config.reviewer_model,
            review_effort=self.config.reviewer_effort,
            max_total_workers=self.config.max_total_workers,
        )

    def _run_stage1_flow(self, flow: Any) -> Any:
        """Run Stage 1 under the campaign-wide Humanize lease.

        Real HumanizeFlow implementations explicitly accept the inherited
        lease. Lightweight factories used by integrations and tests retain
        their historical zero-argument ``run()`` contract; the pipeline itself
        still owns the shared lease while those factories execute.
        """
        run_lease = self._humanize_run_lease
        if run_lease is None:
            raise PipelineError(
                "PIPELINE_LOCK_REQUIRED",
                "Stage 1 cannot run without the campaign-wide Humanize lease",
                stage="stage1_search",
            )
        run_method = flow.run
        try:
            parameters = inspect.signature(run_method).parameters
        except (TypeError, ValueError):
            parameters = {}
        if "inherited_run_lease" in parameters:
            return run_method(inherited_run_lease=run_lease)
        return run_method()

    @contextmanager
    def _exclusive_lock(self) -> Iterable[None]:
        root = _reject_symlink_components(
            self.paths.root,
            classification="UNSAFE_CONTROL_PATH",
            label="pipeline run root",
        )
        root.mkdir(parents=True, exist_ok=True)
        root = _reject_symlink_components(
            root,
            classification="UNSAFE_CONTROL_PATH",
            label="pipeline run root",
        )
        try:
            root_metadata = root.lstat()
        except OSError as exc:
            raise PipelineError(
                "UNSAFE_CONTROL_PATH",
                f"pipeline run root is unavailable: {root}: {exc}",
            ) from exc
        if not stat.S_ISDIR(root_metadata.st_mode):
            raise PipelineError(
                "UNSAFE_CONTROL_PATH",
                f"pipeline run root is not a directory: {root}",
            )
        lock_path = root / "pipeline.lock"
        descriptor = os.open(
            lock_path,
            os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        try:
            if not stat.S_ISREG(os.fstat(descriptor).st_mode):
                raise PipelineError(
                    "UNSAFE_CONTROL_PATH",
                    f"pipeline lock is not a regular file: {lock_path}",
                )
            stream = os.fdopen(descriptor, "a+", encoding="utf-8")
            descriptor = -1
        except BaseException:
            if descriptor >= 0:
                os.close(descriptor)
            raise
        with stream:
            try:
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise PipelineBusyError(
                    "PIPELINE_BUSY",
                    f"another process owns {lock_path}",
                ) from exc
            stream.seek(0)
            stream.truncate()
            stream.write(
                json.dumps({"pid": os.getpid(), "acquired_at": utc_now()}) + "\n"
            )
            stream.flush()
            try:
                store = RunStore.create(
                    self.config.repo_dir / "results",
                    self.config.run_id,
                )
                with ExitStack() as lease_stack:
                    try:
                        run_lease = lease_stack.enter_context(
                            _acquire_humanize_run_lease(store)
                        )
                    except HumanizeRunAlreadyActiveError as exc:
                        raise PipelineBusyError(
                            "PIPELINE_BUSY",
                            "another process owns the shared Humanize run lease "
                            f"for {self.config.run_id!r}",
                        ) from exc
                    except RoundTransactionError as exc:
                        raise PipelineError(
                            "UNSAFE_CONTROL_PATH",
                            f"cannot acquire shared Humanize run lease: {exc}",
                        ) from exc
                    if self._humanize_run_lease is not None:
                        raise PipelineError(
                            "PIPELINE_BUSY",
                            "pipeline already owns a Humanize run lease",
                        )
                    self._humanize_run_lease = run_lease
                    try:
                        yield
                    finally:
                        self._humanize_run_lease = None
            finally:
                fcntl.flock(stream.fileno(), fcntl.LOCK_UN)

    def _source_fingerprint(self, *roots: Path) -> str:
        """Hash imported in-repo Python implementations, including dirty edits."""
        files: set[Path] = set()
        repository = _reject_symlink_components(
            self.config.repo_dir,
            classification="UNSAFE_SOURCE_PATH",
            label="repository source root",
        )
        for original in roots:
            path = _reject_symlink_components(
                original,
                classification="UNSAFE_SOURCE_PATH",
                label="source dependency",
            )
            try:
                path.relative_to(repository)
            except ValueError as exc:
                raise PipelineError(
                    "UNSAFE_SOURCE_PATH",
                    f"source fingerprint path escapes repository: {path}",
                ) from exc
            try:
                metadata = path.lstat()
            except FileNotFoundError as exc:
                raise PipelineError(
                    "INPUT_MISSING", f"source dependency is missing: {path}"
                ) from exc
            except OSError as exc:
                raise PipelineError(
                    "UNSAFE_SOURCE_PATH",
                    f"cannot inspect source dependency {path}: {exc}",
                ) from exc
            if stat.S_ISDIR(metadata.st_mode):
                for original_item in sorted(path.rglob("*")):
                    item = _reject_symlink_components(
                        original_item,
                        classification="UNSAFE_SOURCE_PATH",
                        label="source tree entry",
                    )
                    try:
                        item_metadata = item.lstat()
                    except OSError as exc:
                        raise PipelineError(
                            "UNSAFE_SOURCE_PATH",
                            f"cannot inspect source tree entry {item}: {exc}",
                        ) from exc
                    if stat.S_ISREG(item_metadata.st_mode):
                        if item.suffix == ".py":
                            files.add(item)
                        elif _is_untrusted_import_artifact(item):
                            raise PipelineError(
                                "UNSAFE_SOURCE_PATH",
                                "source tree contains an unhashed executable "
                                f"Python import artifact: {item}",
                            )
                    elif not stat.S_ISDIR(item_metadata.st_mode):
                        raise PipelineError(
                            "UNSAFE_SOURCE_PATH",
                            f"source tree entry is not a regular file or "
                            f"directory: {item}",
                        )
            elif stat.S_ISREG(metadata.st_mode):
                if _is_untrusted_import_artifact(path):
                    raise PipelineError(
                        "UNSAFE_SOURCE_PATH",
                        "source dependency is an untrusted executable Python "
                        f"import artifact: {path}",
                    )
                files.add(path)
            else:
                raise PipelineError(
                    "UNSAFE_SOURCE_PATH",
                    f"source dependency is not a regular file or directory: {path}",
                )
        identities: dict[str, dict[str, Any]] = {}
        for path in sorted(files):
            try:
                identities[str(path)] = _source_file_identity(path)
            except OSError as exc:
                raise PipelineError(
                    "UNSAFE_SOURCE_PATH",
                    f"cannot hash source dependency {path}: {exc}",
                ) from exc
        return _canonical_sha256(identities)

    def _source_file_sha256(self, original: Path, *, label: str) -> str:
        path = _reject_symlink_components(
            original,
            classification="UNSAFE_SOURCE_PATH",
            label=label,
        )
        repository = _lexical_absolute(self.config.repo_dir)
        try:
            path.relative_to(repository)
        except ValueError as exc:
            raise PipelineError(
                "UNSAFE_SOURCE_PATH",
                f"{label} escapes repository: {path}",
            ) from exc
        try:
            metadata = path.lstat()
            if not stat.S_ISREG(metadata.st_mode):
                raise OSError("not a regular file")
            return _file_sha256(path)
        except FileNotFoundError as exc:
            raise PipelineError(
                "INPUT_MISSING", f"{label} is missing: {path}"
            ) from exc
        except OSError as exc:
            raise PipelineError(
                "UNSAFE_SOURCE_PATH",
                f"cannot hash {label} {path}: {exc}",
            ) from exc

    def _audit_source_provenance(self) -> dict[str, Any]:
        registry = self.config.repo_dir / "results" / "known_code_registry.json"
        return {
            "controller_source_sha256": self._source_file_sha256(
                self.config.repo_dir / "humanize" / "pipeline.py",
                label="pipeline controller source",
            ),
            "source_fingerprint": self._source_fingerprint(
                self.config.repo_dir / "humanize" / "pipeline.py",
                self.config.repo_dir / "humanize" / "audit_state.py",
                self.config.repo_dir / "humanize" / "state.py",
                self.config.repo_dir / "evaluation",
                self.config.repo_dir / "scripts" / "audit_candidate_pool.py",
                self.config.repo_dir / "scripts" / "audit_direction_pool.py",
                self.config.repo_dir / "scripts" / "screen_frontier_candidate.py",
                self.config.repo_dir / "scripts" / "screen_frontier_xor.py",
                registry,
            ),
            "known_code_registry_sha256": self._source_file_sha256(
                registry,
                label="known-code registry",
            ),
            **self._worker_runtime_provenance(),
        }

    def _strict_source_provenance(self) -> dict[str, Any]:
        registry = self.config.repo_dir / "results" / "known_code_registry.json"
        runner = self.config.repo_dir / "tests" / "verify_known_answer_gate.py"
        return {
            "controller_source_sha256": self._source_file_sha256(
                self.config.repo_dir / "humanize" / "pipeline.py",
                label="pipeline controller source",
            ),
            "source_fingerprint": self._source_fingerprint(
                self.config.repo_dir / "humanize" / "pipeline.py",
                self.config.repo_dir / "evaluation",
                self.config.repo_dir / "scripts" / "finalize_challenge.py",
                runner,
                registry,
            ),
            "known_code_registry_sha256": self._source_file_sha256(
                registry,
                label="known-code registry",
            ),
            "strict_runner_sha256": self._source_file_sha256(
                runner,
                label="strict known-answer runner",
            ),
            **self._worker_runtime_provenance(),
        }

    def _stage1_source_provenance(self) -> dict[str, Any]:
        return {
            "controller_source_sha256": self._source_file_sha256(
                self.config.repo_dir / "humanize" / "pipeline.py",
                label="pipeline controller source",
            ),
            "source_fingerprint": self._source_fingerprint(
                self.config.repo_dir / "humanize" / "pipeline.py",
                self.config.repo_dir / "humanize" / "flow.py",
                self.config.repo_dir / "humanize" / "audit_state.py",
                self.config.repo_dir / "humanize" / "state.py",
                self.config.repo_dir / "humanize" / "reviewer.py",
                self.config.repo_dir / "evaluation",
                self.config.repo_dir / "evolve",
                self.config.repo_dir / "main.py",
                self.config.repo_dir / "results" / "known_code_registry.json",
            ),
            # HumanizeFlow itself executes in this controller process, while
            # every proof subprocess uses config.python_executable.  Bind both:
            # either environment changing must invalidate Stage 1.
            "controller_runtime": proof_runtime_fingerprint(),
            **self._worker_runtime_provenance(),
        }

    def _worker_runtime_provenance(self) -> dict[str, Any]:
        try:
            provenance = probe_python_runtime(
                self.config.python_executable,
                cwd=self.config.repo_dir,
            )
        except RuntimeProbeError as exc:
            raise PipelineError(
                "RUNTIME_INVALID",
                f"cannot identify configured proof interpreter: {exc}",
            ) from exc
        runtime = provenance.get("runtime")
        interpreter = provenance.get("interpreter")
        if not isinstance(runtime, Mapping) or not isinstance(
            interpreter, Mapping
        ):
            raise PipelineError(
                "RUNTIME_INVALID",
                "configured proof interpreter returned malformed provenance",
            )
        try:
            runtime = validate_proof_runtime_fingerprint(runtime)
        except ValueError as exc:
            raise PipelineError(
                "RUNTIME_INVALID",
                f"configured proof runtime is malformed: {exc}",
            ) from exc
        if runtime["interpreter"] != dict(interpreter):
            raise PipelineError(
                "RUNTIME_INVALID",
                "configured proof runtime has conflicting interpreter identity",
            )
        return {
            "proof_runtime": runtime,
            "proof_interpreter": dict(runtime["interpreter"]),
        }

    @staticmethod
    def _require_inputs_unchanged(
        stage: str,
        inputs: Sequence[Path],
        expected: Mapping[str, str | None],
    ) -> None:
        try:
            current = _hash_paths(inputs)
        except PipelineError as exc:
            raise PipelineError(
                "INPUT_CHANGED_DURING_STAGE",
                f"{stage} input became unavailable or unsafe: {exc}",
                stage=stage,
            ) from exc
        if current != dict(expected):
            raise PipelineError(
                "INPUT_CHANGED_DURING_STAGE",
                f"{stage} inputs changed while the stage was executing",
                stage=stage,
            )

    @staticmethod
    def _require_stage_config_unchanged(
        stage: str,
        expected: Mapping[str, Any],
        revalidator: Callable[[], Mapping[str, Any]] | None,
    ) -> None:
        """Replay dynamic source provenance after execution and cache validation."""

        if revalidator is None:
            return
        try:
            observed = dict(revalidator())
        except PipelineError as exc:
            raise PipelineError(
                "INPUT_CHANGED_DURING_STAGE",
                f"{stage} source provenance became unavailable or unsafe: {exc}",
                stage=stage,
            ) from exc
        except Exception as exc:
            raise PipelineError(
                "INPUT_CHANGED_DURING_STAGE",
                f"{stage} source provenance could not be replayed: "
                f"{type(exc).__name__}: {exc}",
                stage=stage,
            ) from exc
        if observed != dict(expected):
            raise PipelineError(
                "INPUT_CHANGED_DURING_STAGE",
                f"{stage} source provenance changed while the stage was executing",
                stage=stage,
            )

    def _clear_stage_outputs(
        self,
        stage: str,
        outputs: Sequence[Path],
    ) -> None:
        """Remove stale pipeline-owned outputs before a new machine attempt."""
        root = self.paths.root.resolve()
        for original in outputs:
            path = Path(original)
            resolved = path.resolve(strict=False)
            try:
                resolved.relative_to(root)
            except ValueError as exc:
                raise PipelineError(
                    "UNSAFE_OUTPUT_PATH",
                    f"{stage} output escapes pipeline root: {path}",
                    stage=stage,
                ) from exc
            if path.is_symlink():
                raise PipelineError(
                    "UNSAFE_OUTPUT_PATH",
                    f"{stage} output may not be a symlink: {path}",
                    stage=stage,
                )
            if path.exists():
                if not path.is_file():
                    raise PipelineError(
                        "UNSAFE_OUTPUT_PATH",
                        f"{stage} output is not a regular file: {path}",
                        stage=stage,
                    )
                path.unlink()

    def _stage_config_fingerprint(
        self,
        command: Sequence[str],
        stage_config: Mapping[str, Any],
    ) -> str:
        return _canonical_sha256(
            {"command": list(command), "stage_config": dict(stage_config)}
        )

    def _machine_cache_valid(
        self,
        stage: str,
        *,
        fingerprint: str,
        stage_config: Mapping[str, Any],
        input_hashes: Mapping[str, str | None],
    ) -> bool:
        if not self.config.resume:
            return False
        record = self.state["stages"][stage]
        if record.get("machine_status") not in {"COMPLETED", "SKIPPED"}:
            return False
        if record.get("stage_fingerprint") != fingerprint:
            return False
        if record.get("stage_config") != dict(stage_config):
            return False
        if record.get("input_hashes") != dict(input_hashes):
            return False
        outputs = record.get("output_hashes")
        if not isinstance(outputs, dict):
            return False
        for path_text, expected in outputs.items():
            try:
                current = _hash_paths(
                    [Path(path_text)],
                    require=False,
                    classification="UNSAFE_OUTPUT_PATH",
                    label=f"{stage} cached output",
                )[str(_lexical_absolute(path_text))]
            except PipelineError:
                return False
            if current != expected:
                return False
        return True

    def _invalidate_downstream(self, stage: str, reason: str) -> None:
        start = STAGE_ORDER.index(stage) + 1
        for name in STAGE_ORDER[start:]:
            record = self.state["stages"][name]
            if record.get("machine_status") != "PENDING":
                record["status"] = "INVALIDATED"
                record["machine_status"] = "INVALIDATED"
                record["review_status"] = "INVALIDATED"
                record["invalidated_at"] = utc_now()
                record["invalidation_reason"] = reason
        self._write_state()

    def _run_command(self, stage: str, command: list[str], log_path: Path) -> int:
        try:
            completed = self.command_runner(command, cwd=self.config.repo_dir)
        except FileNotFoundError as exc:
            raise PipelineError("COMMAND_NOT_FOUND", str(exc), stage=stage) from exc
        except subprocess.TimeoutExpired as exc:
            raise PipelineError("STAGE_TIMEOUT", str(exc), stage=stage) from exc
        except OSError as exc:
            raise PipelineError("COMMAND_LAUNCH_ERROR", str(exc), stage=stage) from exc
        stdout = completed.stdout if isinstance(completed.stdout, str) else ""
        stderr = completed.stderr if isinstance(completed.stderr, str) else ""
        _atomic_write_text(
            log_path,
            stdout + (("\n[stderr]\n" + stderr) if stderr else ""),
        )
        return int(completed.returncode)

    @staticmethod
    def _compact_context(value: Mapping[str, Any]) -> dict[str, Any]:
        context = {
            key: item
            for key, item in value.items()
            if key not in {"results", "evaluations"}
        }
        rows = value.get("results", value.get("evaluations", []))
        if isinstance(rows, list):
            context["result_count"] = len(rows)
            context["result_sample"] = rows[:8]
        return context

    def _review_stage(
        self,
        stage: str,
        context: Mapping[str, Any],
    ) -> None:
        record = self.state["stages"][stage]
        if not self.config.stage_review:
            record["review_status"] = "DISABLED"
            record["status"] = record["machine_status"]
            record["finished_at"] = utc_now()
            self._write_state()
            return
        review_fingerprint = _canonical_sha256(
            {
                "prompt_version": REVIEW_PROMPT_VERSION,
                "model": self.config.reviewer_model,
                "effort": self.config.reviewer_effort,
            }
        )
        if (
            self.config.resume
            and record.get("review_status") == "COMPLETED"
            and record.get("review_machine_output_hashes")
            == record.get("output_hashes")
            and record.get("review_fingerprint") == review_fingerprint
        ):
            record["status"] = record["machine_status"]
            record["finished_at"] = utc_now()
            self._write_state()
            return

        review_dir = self.paths.reviews / stage
        review_dir.mkdir(parents=True, exist_ok=True)
        prompt = (
            "You are an independent advisory reviewer for a deterministic qcode "
            f"campaign checkpoint ({stage}). Review only the machine evidence "
            "below. You cannot alter routing, upgrade UNRESOLVED or any distance "
            "claim, waive certificate_passed/verification_passed, or bypass the "
            "Stage 5 strict known-answer gate. A promote/stop verdict is advice "
            "only. Flag corrupt evidence, partial proof coverage, resource risks, "
            "and useful next actions.\n\nMachine evidence JSON:\n"
            + json.dumps(
                self._compact_context(context),
                ensure_ascii=False,
                indent=2,
                default=str,
            )
            + "\n"
        )
        _atomic_write_text(review_dir / "prompt.md", prompt)
        record["review_attempt"] = int(record.get("review_attempt", 0)) + 1
        record["review_status"] = "RUNNING"
        record["review_started_at"] = utc_now()
        record["review_path"] = str(review_dir / "review.json")
        record["review_fingerprint"] = review_fingerprint
        self._write_state()
        try:
            if stage != "stage1_search":
                # A refreshed advisory review must not leave an older successful
                # artifact looking current when the new attempt later fails.
                for name in ("review.json", "bitlesson-suggestions.json"):
                    (review_dir / name).unlink(missing_ok=True)
                record.pop("review_machine_output_hashes", None)
                record.pop("bitlesson_ids", None)
            reviewer = self.reviewer
            if reviewer is None:
                raise RuntimeError("stage review is enabled without a reviewer")
            method = reviewer.review if hasattr(reviewer, "review") else reviewer
            parameters = inspect.signature(method).parameters
            if "stage" in parameters or len(parameters) >= 3:
                review = method(stage, prompt, review_dir)
            else:
                review = method(prompt, review_dir)
            review = validate_review(review)
            atomic_write_json(review_dir / "review.json", review)
            atomic_write_json(
                review_dir / "bitlesson-suggestions.json",
                {
                    "stage": stage,
                    "generated_at": utc_now(),
                    "advisory_only": True,
                    "lessons": review["lessons"],
                },
            )
            if review["verdict"] != "reject_round":
                lesson_store = RunStore.create(
                    self.config.repo_dir / "results", self.config.run_id
                )
                record["bitlesson_ids"] = lesson_store.add_lessons(
                    review["lessons"], STAGE_ORDER.index(stage) + 1
                )
        except Exception as exc:
            finished_at = utc_now()
            error = f"{type(exc).__name__}: {exc}"
            record["review_finished_at"] = finished_at
            record["review_error"] = error
            if stage == "stage1_search":
                # Stage 1's reviewer participates in the search loop and keeps
                # its existing fail-closed semantics.
                record["review_status"] = "FAILED"
                record["status"] = "REVIEW_FAILED"
                self._write_state()
                raise PipelineError(
                    "REVIEW_FAILED",
                    error,
                    stage=stage,
                ) from exc

            # Reviews after search are advisory by contract. Record the failure
            # durably, but preserve the deterministic machine result and routing.
            for name in ("review.json", "bitlesson-suggestions.json"):
                try:
                    (review_dir / name).unlink(missing_ok=True)
                except OSError:
                    # State is authoritative; a stale artifact is never accepted
                    # unless review_status is COMPLETED with matching hashes.
                    pass
            record["review_status"] = "ADVISORY_FAILED"
            record["advisory_failure"] = {
                "classification": "ADVISORY_FAILED",
                "error": error,
                "attempt": record["review_attempt"],
                "timestamp": finished_at,
            }
            record["status"] = record["machine_status"]
            record["finished_at"] = finished_at
            self._write_state()
            return
        record["review_status"] = "COMPLETED"
        record["review_finished_at"] = utc_now()
        record.pop("review_error", None)
        record.pop("advisory_failure", None)
        record["review_machine_output_hashes"] = record.get("output_hashes", {})
        record["status"] = record["machine_status"]
        record["finished_at"] = utc_now()
        self._write_state()

    def _execute_stage(
        self,
        stage: str,
        *,
        command: list[str],
        stage_config: Mapping[str, Any],
        stage_config_revalidator: Callable[[], Mapping[str, Any]] | None = None,
        inputs: Sequence[Path],
        outputs: Sequence[Path],
        machine: Callable[[], int],
        validator: Callable[[], Mapping[str, Any]],
        recoverable_exit_codes: frozenset[int] = frozenset(),
        nonzero_validator: Callable[[], Mapping[str, Any]] | None = None,
        machine_status: str = "COMPLETED",
    ) -> dict[str, Any]:
        self._ensure_solver_state_tree_safe()
        self._require_stage_config_unchanged(
            stage, stage_config, stage_config_revalidator
        )
        input_hashes = _hash_paths(inputs)
        fingerprint = self._stage_config_fingerprint(command, stage_config)
        record = self.state["stages"][stage]
        cache_valid = self._machine_cache_valid(
            stage,
            fingerprint=fingerprint,
            stage_config=stage_config,
            input_hashes=input_hashes,
        )
        if not cache_valid:
            self._invalidate_downstream(stage, f"{stage} machine cache changed")
            record["attempt"] = int(record.get("attempt", 0)) + 1
            record["status"] = "RUNNING"
            record["machine_status"] = "RUNNING"
            record["started_at"] = utc_now()
            record["command"] = command
            record["command_sha256"] = _canonical_sha256(command)
            record["stage_config"] = dict(stage_config)
            record["stage_fingerprint"] = fingerprint
            record["input_hashes"] = input_hashes
            record["exit_code"] = None
            record.pop("failure", None)
            record.pop("incomplete_at", None)
            record.pop("incomplete_reasons", None)
            self.state["active_stage"] = stage
            self._write_state()
            try:
                self._clear_stage_outputs(stage, outputs)
                exit_code = machine()
                record["exit_code"] = exit_code
                self._require_inputs_unchanged(stage, inputs, input_hashes)
                if exit_code != 0:
                    if (
                        exit_code not in recoverable_exit_codes
                        or nonzero_validator is None
                    ):
                        classification = (
                            "STRICT_GATE_REJECTED"
                            if stage == "stage5_strict_gate" and exit_code == 1
                            else "STAGE_EXIT_NONZERO"
                        )
                        raise PipelineError(
                            classification,
                            f"{stage} exited with status {exit_code}",
                            stage=stage,
                            exit_code=exit_code,
                        )
                    context = dict(nonzero_validator())
                    record["accepted_nonzero_output"] = True
                else:
                    context = dict(validator())
                    record.pop("accepted_nonzero_output", None)
                output_hashes = _hash_paths(
                    outputs,
                    classification="UNSAFE_OUTPUT_PATH",
                    label=f"{stage} output",
                )
                self._require_inputs_unchanged(stage, inputs, input_hashes)
                self._require_stage_config_unchanged(
                    stage, stage_config, stage_config_revalidator
                )
            except PipelineError:
                raise
            except Exception as exc:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{type(exc).__name__}: {exc}",
                    stage=stage,
                ) from exc
            record["machine_status"] = machine_status
            record["machine_completed_at"] = utc_now()
            record["output_hashes"] = output_hashes
            record["machine_summary"] = self._compact_context(context)
            record["resumed_machine"] = False
            self._write_state()
        else:
            try:
                if (
                    record.get("accepted_nonzero_output") is True
                    and record.get("exit_code") in recoverable_exit_codes
                    and nonzero_validator is not None
                ):
                    context = dict(nonzero_validator())
                else:
                    context = dict(validator())
                self._require_inputs_unchanged(stage, inputs, input_hashes)
                self._require_stage_config_unchanged(
                    stage, stage_config, stage_config_revalidator
                )
            except PipelineError:
                raise
            except Exception as exc:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{type(exc).__name__}: {exc}",
                    stage=stage,
                ) from exc
            record["resumed_machine"] = True
            record["status"] = record["machine_status"]
            self.state["active_stage"] = stage
            self._write_state()
        self._review_stage(stage, context)
        self.state["active_stage"] = None
        self._write_state()
        return context

    def _stage1_inputs(self) -> list[Path]:
        stage = "stage1_search"
        if self.config.candidate_inputs:
            candidates = list(self.config.candidate_inputs)
            command = ["internal:existing-candidate-inputs", *map(str, candidates)]

            def current_stage_config() -> dict[str, Any]:
                return {
                    "mode": "existing-inputs",
                    # There is no Humanize search implementation in this mode,
                    # but the handoff still belongs to the proof campaign and
                    # must be invalidated when either process environment
                    # changes.
                    "controller_runtime": proof_runtime_fingerprint(),
                    **self._worker_runtime_provenance(),
                }

            stage_config = current_stage_config()
            stage_config_revalidator = current_stage_config
            machine = lambda: 0
        else:
            flow_config = self._flow_config()
            flow_holder: dict[str, Any] = {}
            command = ["internal:HumanizeFlow.run", self.config.run_id]

            def current_stage_config() -> dict[str, Any]:
                return {
                    "mode": "humanize-flow",
                    "flow_config": flow_config.serializable(),
                    **self._stage1_source_provenance(),
                }

            stage_config = current_stage_config()
            stage_config_revalidator = current_stage_config

            def machine() -> int:
                # Both settings are process-global. Serialize in-process
                # campaigns so concurrent run_ids cannot interleave restore
                # operations while a spawn worker inherits the environment.
                with _PYCACHE_ENVIRONMENT_LOCK:
                    with tempfile.TemporaryDirectory(
                        prefix="qcode-stage1-pycache-"
                    ) as cache:
                        previous_cache_prefix = sys.pycache_prefix
                        cache_environment_present = (
                            "PYTHONPYCACHEPREFIX" in os.environ
                        )
                        previous_cache_environment = os.environ.get(
                            "PYTHONPYCACHEPREFIX"
                        )
                        sys.pycache_prefix = cache
                        os.environ["PYTHONPYCACHEPREFIX"] = cache
                        try:
                            flow = self.flow_factory(flow_config)
                            flow_holder["flow"] = flow
                            try:
                                flow_state = self._run_stage1_flow(flow)
                            except UnresolvedAuditError:
                                store = getattr(flow, "store", None)
                                loader = getattr(store, "load_state", None)
                                flow_state = (
                                    loader() if callable(loader) else None
                                )
                                if (
                                    not isinstance(flow_state, Mapping)
                                    or flow_state.get("status")
                                    != "incomplete-unresolved"
                                ):
                                    raise
                        finally:
                            sys.pycache_prefix = previous_cache_prefix
                            if cache_environment_present:
                                assert previous_cache_environment is not None
                                os.environ["PYTHONPYCACHEPREFIX"] = (
                                    previous_cache_environment
                                )
                            else:
                                os.environ.pop("PYTHONPYCACHEPREFIX", None)
                if (
                    not isinstance(flow_state, Mapping)
                    or flow_state.get("status")
                    not in {"search-complete", "incomplete-unresolved"}
                ):
                    raise PipelineError(
                        "STAGE1_INCOMPLETE",
                        "HumanizeFlow produced no auditable Stage 1 handoff",
                        stage=stage,
                    )
                flow_holder["state"] = flow_state
                return 0

            candidates = []

        input_paths = (
            list(self.config.candidate_inputs)
            if self.config.candidate_inputs
            else [
                path
                for path in (
                    self._flow_config().evolution_config,
                    self._flow_config().evolution_seed,
                    self._flow_config().candidate_file,
                )
                if path is not None
            ]
        )
        fingerprint = self._stage_config_fingerprint(command, stage_config)
        input_hashes = _hash_paths(input_paths)
        record = self.state["stages"][stage]
        cache_valid = self._machine_cache_valid(
            stage,
            fingerprint=fingerprint,
            stage_config=stage_config,
            input_hashes=input_hashes,
        )
        if cache_valid:
            output_paths = [Path(path) for path in record["output_hashes"]]
            self._require_inputs_unchanged(stage, input_paths, input_hashes)
            self._require_stage_config_unchanged(
                stage, stage_config, stage_config_revalidator
            )
            record["resumed_machine"] = True
            record["status"] = record["machine_status"]
            self._write_state()
            if self.config.candidate_inputs:
                self._review_stage(
                    stage,
                    {
                        "gate": "qcode-stage1-existing-candidates",
                        "candidate_inputs": [str(path) for path in output_paths],
                        "input_hashes": record["output_hashes"],
                    },
                )
            return output_paths

        self._invalidate_downstream(stage, "Stage 1 machine cache changed")
        record["attempt"] = int(record.get("attempt", 0)) + 1
        record["status"] = "RUNNING"
        record["machine_status"] = "RUNNING"
        record["started_at"] = utc_now()
        record["command"] = command
        record["command_sha256"] = _canonical_sha256(command)
        record["stage_config"] = dict(stage_config)
        record["stage_fingerprint"] = fingerprint
        record["input_hashes"] = input_hashes
        record["exit_code"] = None
        self.state["active_stage"] = stage
        self._write_state()
        try:
            exit_code = machine()
            self._require_inputs_unchanged(stage, input_paths, input_hashes)
            self._require_stage_config_unchanged(
                stage, stage_config, stage_config_revalidator
            )
            if exit_code != 0:
                raise PipelineError(
                    "STAGE_EXIT_NONZERO",
                    f"Stage 1 exited with status {exit_code}",
                    stage=stage,
                    exit_code=exit_code,
                )
            if not self.config.candidate_inputs:
                flow = flow_holder["flow"]
                returned = flow_holder.get("state")
                candidates = self._discover_flow_outputs(flow, returned)
            if not candidates:
                raise PipelineError(
                    "OUTPUT_MISSING",
                    "Stage 1 produced no candidate input path",
                    stage=stage,
                )
            output_hashes = _hash_paths(candidates)
            self._require_inputs_unchanged(stage, input_paths, input_hashes)
            self._require_stage_config_unchanged(
                stage, stage_config, stage_config_revalidator
            )
        except PipelineError:
            raise
        except Exception as exc:
            raise PipelineError(
                "STAGE1_FAILED",
                f"{type(exc).__name__}: {exc}",
                stage=stage,
            ) from exc
        record["exit_code"] = 0
        record["machine_status"] = "COMPLETED"
        record["status"] = "COMPLETED"
        record["machine_completed_at"] = utc_now()
        record["output_hashes"] = output_hashes
        record["candidate_inputs"] = [str(path) for path in candidates]
        record["review_status"] = (
            "MANAGED_BY_HUMANIZE" if not self.config.candidate_inputs else "PENDING"
        )
        record["finished_at"] = utc_now()
        record["resumed_machine"] = False
        self._write_state()
        if self.config.candidate_inputs:
            self._review_stage(
                stage,
                {
                    "gate": "qcode-stage1-existing-candidates",
                    "candidate_inputs": [str(path) for path in candidates],
                    "input_hashes": output_hashes,
                },
            )
        self.state["active_stage"] = None
        self._write_state()
        return candidates

    def _discover_flow_outputs(
        self,
        flow: Any,
        returned: Any,
    ) -> list[Path]:
        values: Any = None
        if isinstance(returned, Mapping):
            values = returned.get(
                "pipeline_candidate_inputs", returned.get("candidate_inputs")
            )
        if values is None and hasattr(flow, "pipeline_candidate_inputs"):
            values = flow.pipeline_candidate_inputs
        if values is None and hasattr(flow, "candidate_log"):
            values = [flow.candidate_log]
        if values is None and self._flow_config().candidate_file is not None:
            values = [self._flow_config().candidate_file]
        if values is None:
            values = [
                self.config.repo_dir
                / "results"
                / "evolution"
                / f"humanize_{self.config.run_id}"
                / "all_codes.jsonl"
            ]
        if isinstance(values, (str, os.PathLike, Path)):
            values = [values]
        return [_resolve_path(value, self.config.repo_dir) for value in values]

    def _scaled_proof_timeout(self, value: float) -> float:
        """Scale proof time only; retry attempts never increase concurrency."""

        scaled = float(value) * float(self._proof_budget_multiplier)
        if not math.isfinite(scaled) or scaled <= 0:
            raise PipelineError(
                "INVALID_PROOF_RETRY_BUDGET",
                "scaled proof timeout must be positive and finite",
            )
        return scaled

    def _scaled_strict_timeout(self, value: float) -> int | float:
        """Scale a Stage 5 float budget without changing its 1x command shape."""

        if float(self._proof_budget_multiplier) == 1.0:
            return value
        return self._scaled_proof_timeout(value)

    def _scaled_strict_integer_timeout(self, value: int) -> int:
        """Scale one argparse integer timeout for the strict IBM replay."""

        scaled = float(value) * float(self._proof_budget_multiplier)
        if not math.isfinite(scaled) or scaled <= 0:
            raise PipelineError(
                "INVALID_PROOF_RETRY_BUDGET",
                "scaled strict integer timeout must be positive and finite",
            )
        return max(1, math.ceil(scaled))

    def _stage2_command(self, candidates: Sequence[Path]) -> list[str]:
        command = [
            self.config.python_executable,
            "-I",
            "-B",
            str(self.config.repo_dir / "scripts" / "audit_candidate_pool.py"),
            *map(str, candidates),
            "--top",
            str(self.config.stage2_top),
            "--state-dir",
            str(self.paths.solver_state),
            "--ranked-output",
            str(self.paths.stage2_ranked),
            "--summary-output",
            str(self.paths.stage2_summary),
            "--selection-ledger",
            str(self.paths.stage2_selection_ledger),
            "--timeout",
            str(self._scaled_proof_timeout(self.config.stage2_timeout)),
            "--candidate-workers",
            str(self.config.stage2_candidate_workers),
            "--solver-workers",
            str(self.config.stage2_solver_workers),
            "--certificate-workers",
            str(self.config.certificate_workers),
            "--certificate-solver-workers",
            str(self.config.certificate_solver_workers),
            "--max-total-workers",
            str(self.config.max_total_workers),
            "--certify",
            "--known-answer-artifact",
            str(self.config.known_answer_artifact),
            "--certificate-timeout-per-logical",
            str(
                self._scaled_proof_timeout(
                    self.config.certificate_timeout_per_logical
                )
            ),
            "--certificate-total-timeout",
            str(
                self._scaled_proof_timeout(
                    self.config.certificate_total_timeout
                )
            ),
            "--verification-timeout-per-logical",
            str(
                self._scaled_proof_timeout(
                    self.config.verification_timeout_per_logical
                )
            ),
            "--verification-total-timeout",
            str(
                self._scaled_proof_timeout(
                    self.config.verification_total_timeout
                )
            ),
            "--resume" if self.config.resume else "--no-resume",
        ]
        return command

    def _write_skipped_stage3(self, stage2: Mapping[str, Any]) -> int:
        """Materialize a durable empty Stage 3 without starting a solver."""

        _atomic_write_text(
            self.paths.stage3_ranked,
            self.paths.stage2_ranked.read_text(),
        )
        _atomic_write_text(self.paths.stage3_thresholds, "")
        summary = {
            "schema_version": 1,
            "gate": "qldpc-direction-candidate-pool",
            "skipped": True,
            "skip_reason": "Stage 2 produced no UNRESOLVED candidates",
            "input_rows": int(stage2.get("unique_candidates", 0) or 0),
            "selected_candidates": 0,
            "selection_exhausted": True,
            "malformed_unresolved_rows": 0,
            "duplicate_digests_skipped": 0,
            "threshold_only": not self.config.stage3_exact,
            "status_counts": {},
            "certify": True,
            "stage4_candidates": 0,
            "certified_wins": 0,
            "operational_errors": 0,
            "stage4_manifest": str(self.paths.stage3_thresholds),
            "ranked_output": str(self.paths.stage3_ranked),
            "state_dir": str(self.paths.solver_state),
            "results": [],
        }
        atomic_write_json(self.paths.stage3_summary, summary)
        return 0

    def _stage3_command(self) -> list[str]:
        command = [
            self.config.python_executable,
            "-I",
            "-B",
            str(self.config.repo_dir / "scripts" / "audit_direction_pool.py"),
            str(self.paths.stage2_ranked),
            "--state-dir",
            str(self.paths.solver_state),
            "--ranked-output",
            str(self.paths.stage3_ranked),
            "--summary-output",
            str(self.paths.stage3_summary),
            "--stage4-manifest",
            str(self.paths.stage3_thresholds),
            "--top",
            str(self.config.stage3_top),
            "--timeout",
            str(self._scaled_proof_timeout(self.config.stage3_timeout)),
            "--candidate-workers",
            str(self.config.stage3_candidate_workers),
            "--direction-workers",
            str(self.config.stage3_direction_workers),
            "--max-total-workers",
            str(self.config.max_total_workers),
            "--certify",
            "--certificate-workers",
            str(self.config.certificate_workers),
            "--certificate-solver-workers",
            str(self.config.certificate_solver_workers),
            "--known-answer-artifact",
            str(self.config.known_answer_artifact),
            "--certificate-timeout-per-logical",
            str(
                self._scaled_proof_timeout(
                    self.config.certificate_timeout_per_logical
                )
            ),
            "--certificate-total-timeout",
            str(
                self._scaled_proof_timeout(
                    self.config.certificate_total_timeout
                )
            ),
            "--verification-timeout-per-logical",
            str(
                self._scaled_proof_timeout(
                    self.config.verification_timeout_per_logical
                )
            ),
            "--verification-total-timeout",
            str(
                self._scaled_proof_timeout(
                    self.config.verification_total_timeout
                )
            ),
            "--resume" if self.config.resume else "--no-resume",
        ]
        if self.config.stage3_exact:
            command.append("--exact")
        return command

    @staticmethod
    def _validate_pool_summary(
        path: Path,
        ranked: Path,
        expected_gate: str,
        *,
        allow_operational_errors: bool = False,
    ) -> dict[str, Any]:
        summary = _read_json_object(path)
        if summary.get("gate") != expected_gate:
            raise PipelineError(
                "OUTPUT_INVALID",
                f"{path} has unexpected gate {summary.get('gate')!r}",
            )
        results = summary.get("results")
        if not isinstance(results, list):
            raise PipelineError("OUTPUT_INVALID", f"{path}.results must be a list")
        if not ranked.is_file():
            raise PipelineError("OUTPUT_MISSING", f"missing ranked output: {ranked}")

        allowed_statuses = {
            "UNSUPPORTED",
            "REJECTED",
            "THRESHOLD_PROVEN",
            "EXACT_PROVEN",
            "UNRESOLVED",
            "ERROR",
        }
        results_by_digest: dict[str, dict[str, Any]] = {}
        computed_counts: dict[str, int] = {}
        for index, raw_result in enumerate(results):
            if not isinstance(raw_result, Mapping):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.results[{index}] must be an object",
                )
            result = dict(raw_result)
            digest = result.get("canonical_digest")
            status = result.get("status")
            if not isinstance(digest, str) or not digest:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.results[{index}] lacks canonical_digest",
                )
            if digest in results_by_digest:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path} contains duplicate canonical_digest {digest!r}",
                )
            if status not in allowed_statuses:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.results[{index}] has invalid status {status!r}",
                )
            results_by_digest[digest] = result
            computed_counts[str(status)] = computed_counts.get(str(status), 0) + 1

        reported_counts = summary.get("status_counts")
        if not isinstance(reported_counts, Mapping):
            raise PipelineError(
                "OUTPUT_INVALID", f"{path}.status_counts must be an object"
            )
        normalized_counts: dict[str, int] = {}
        for status, count in reported_counts.items():
            if (
                str(status) not in allowed_statuses
                or isinstance(count, bool)
                or not isinstance(count, int)
                or count < 0
            ):
                raise PipelineError(
                    "OUTPUT_INVALID", f"{path} has invalid status_counts"
                )
            if count:
                normalized_counts[str(status)] = count
        if normalized_counts != computed_counts:
            raise PipelineError(
                "OUTPUT_INVALID",
                f"{path}.status_counts does not match results",
            )

        operational_error_total = 0
        for field_name in (
            "operational_errors",
            "certificate_operational_errors",
        ):
            if field_name not in summary:
                continue
            count = summary[field_name]
            if isinstance(count, bool) or not isinstance(count, int) or count < 0:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.{field_name} must be a non-negative integer",
                )
            operational_error_total += count
        has_operational_errors = bool(
            operational_error_total or computed_counts.get("ERROR", 0)
        )
        if has_operational_errors and not allow_operational_errors:
            raise PipelineError(
                "OPERATIONAL_ERROR", f"{path} reports solver operational errors"
            )

        annotation_key = (
            "campaign_audit"
            if expected_gate == "qldpc-proof-oriented-candidate-pool"
            else "campaign_direction_audit"
        )
        selection_key = (
            "campaign_selected"
            if expected_gate == "qldpc-proof-oriented-candidate-pool"
            else "campaign_direction_selected"
        )
        ranked_results: dict[str, dict[str, Any]] = {}
        selected_digests: set[str] = set()
        try:
            lines = ranked.read_text().splitlines()
        except OSError as exc:
            raise PipelineError(
                "OUTPUT_INVALID", f"cannot read ranked output {ranked}: {exc}"
            ) from exc
        for line_number, line in enumerate(lines, start=1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked}:{line_number} is not valid JSON: {exc}",
                ) from exc
            if not isinstance(row, dict):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked}:{line_number} must contain an object",
                )
            selection_identity = row.get("triage_identity")
            selection_row_digests = [
                str(value)
                for value in (
                    selection_identity.get("canonical_digest")
                    if isinstance(selection_identity, Mapping)
                    else None,
                    row.get("canonical_digest"),
                )
                if value is not None
            ]
            selection = row.get(selection_key)
            if selection is not None and not isinstance(selection, bool):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked}:{line_number}.{selection_key} must be boolean",
                )
            if selection is True:
                if not selection_row_digests:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{ranked}:{line_number} selects a row without a digest",
                    )
                if len(set(selection_row_digests)) != 1:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{ranked}:{line_number} has conflicting candidate digests",
                    )
                selected_digests.add(selection_row_digests[0])
            annotation = row.get(annotation_key)
            if annotation is None:
                continue
            if not isinstance(annotation, Mapping):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked}:{line_number}.{annotation_key} must be an object",
                )
            annotation = dict(annotation)
            digest = annotation.get("canonical_digest")
            if not isinstance(digest, str) or not digest:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked}:{line_number}.{annotation_key} lacks canonical_digest",
                )
            identity = row.get("triage_identity")
            row_digests = [
                str(value)
                for value in (
                    identity.get("canonical_digest")
                    if isinstance(identity, Mapping)
                    else None,
                    row.get("canonical_digest"),
                )
                if value is not None
            ]
            if not row_digests:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked}:{line_number} lacks a candidate digest",
                )
            if any(value != digest for value in row_digests):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked}:{line_number} binds audit to the wrong candidate",
                )
            if digest in ranked_results:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{ranked} repeats {annotation_key} for {digest!r}",
                )
            ranked_results[digest] = annotation
        selected_count = summary.get("selected_candidates")
        if (
            isinstance(selected_count, bool)
            or not isinstance(selected_count, int)
            or selected_count < 0
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                f"{path}.selected_candidates must be a non-negative integer",
            )
        if ranked_results != results_by_digest:
            raise PipelineError(
                "OUTPUT_INVALID",
                f"{path}.results is not exactly bound to {ranked} annotations",
            )
        if selected_count != len(selected_digests) or selected_digests != set(
            results_by_digest
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                f"{path} selection markers do not match audited results",
            )
        selection_exhausted = summary.get("selection_exhausted")
        if not isinstance(selection_exhausted, bool):
            raise PipelineError(
                "OUTPUT_INVALID",
                f"{path}.selection_exhausted must be boolean",
            )
        selection_page = summary.get("selection_page")
        if selection_page is not None:
            if expected_gate != "qldpc-proof-oriented-candidate-pool":
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path} unexpectedly contains a Stage 2 selection page",
                )
            if not isinstance(selection_page, Mapping):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.selection_page must be an object",
                )
            binding = selection_page.get("binding_sha256")
            start_index = selection_page.get("start_index")
            next_index = selection_page.get("next_index")
            page_digests = selection_page.get("selected_digests")
            page_sha256 = selection_page.get("page_sha256")
            if (
                not isinstance(binding, str)
                or not re.fullmatch(r"[0-9a-f]{64}", binding)
                or isinstance(start_index, bool)
                or not isinstance(start_index, int)
                or start_index < 0
                or isinstance(next_index, bool)
                or not isinstance(next_index, int)
                or next_index < start_index
                or not isinstance(page_digests, list)
                or any(
                    not isinstance(item, str) or not item
                    for item in page_digests
                )
                or len(set(page_digests)) != len(page_digests)
                or page_digests
                != [
                    str(result["canonical_digest"])
                    for result in results
                ]
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.selection_page is malformed",
                )
            expected_page_sha256 = _audit_json_sha256({
                "binding_sha256": binding,
                "start_index": start_index,
                "next_index": next_index,
                "selected_digests": page_digests,
            })
            if page_sha256 != expected_page_sha256:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.selection_page has an invalid page hash",
                )
        return summary

    @classmethod
    def _validate_recoverable_pool_summary(
        cls,
        path: Path,
        ranked: Path,
        expected_gate: str,
    ) -> dict[str, Any]:
        """Validate a proof CLI's exit-2 artifact without trusting its flags.

        Solver/certificate errors are retained as incomplete proof work.  The
        only route from such an artifact to WIN is the independent Stage 4
        certificate replay below; a poison-only artifact therefore remains
        fail closed.
        """

        summary = cls._validate_pool_summary(
            path,
            ranked,
            expected_gate,
            allow_operational_errors=True,
        )
        counts = summary.get("status_counts")
        reported_error = bool(
            isinstance(counts, Mapping)
            and isinstance(counts.get("ERROR", 0), int)
            and not isinstance(counts.get("ERROR", 0), bool)
            and counts.get("ERROR", 0) > 0
        )
        for field in (
            "operational_errors",
            "certificate_operational_errors",
        ):
            value = summary.get(field, 0)
            reported_error = reported_error or bool(
                isinstance(value, int)
                and not isinstance(value, bool)
                and value > 0
            )
        if not reported_error:
            raise PipelineError(
                "STAGE_EXIT_NONZERO",
                f"{path} exited 2 without a bound operational-error record",
                stage=(
                    "stage2_sector_audit"
                    if expected_gate == "qldpc-proof-oriented-candidate-pool"
                    else "stage3_direction_audit"
                ),
                exit_code=2,
            )
        return summary

    @staticmethod
    def _certificate_rows(
        summary: Mapping[str, Any], source: str
    ) -> list[dict[str, Any]]:
        rows: list[dict[str, Any]] = []
        for result in summary.get("results", []):
            if not isinstance(result, Mapping):
                continue
            certificate = result.get("certificate")
            if not isinstance(certificate, Mapping):
                continue
            attempted = certificate.get("attempted") is True
            exact = certificate.get("certificate_exact") is True
            build_passed = certificate.get("certificate_passed") is True
            verification_passed = certificate.get("verification_passed") is True
            if (build_passed and not exact) or (
                verification_passed and not build_passed
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "certificate summary contains inconsistent proof flags",
                    stage="stage4_certificate_merge",
                )
            if not (attempted and exact and build_passed and verification_passed):
                continue
            rows.append(
                {
                    "source_stage": source,
                    "canonical_digest": str(result.get("canonical_digest", "")),
                    "certificate": dict(certificate),
                }
            )
        return rows

    @staticmethod
    def _certificate_requires_retry(result: Mapping[str, Any]) -> bool:
        """Return true when a threshold proof still lacks a terminal certificate."""

        if result.get("status") not in {"THRESHOLD_PROVEN", "EXACT_PROVEN"}:
            return False
        certificate = result.get("certificate")
        if (
            not isinstance(certificate, Mapping)
            or certificate.get("attempted") is not True
            or certificate.get("certificate_exact") is not True
        ):
            return True
        if certificate.get("certificate_passed") is False:
            # Exact construction can conclusively show that the candidate does
            # not pass the challenge gate; independent replay is then skipped.
            return False
        return not (
            certificate.get("certificate_passed") is True
            and certificate.get("verification_passed") is True
        )

    @classmethod
    def _proof_incompleteness(
        cls,
        stage2: Mapping[str, Any],
        stage3: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Describe proof work that forbids an exhaustive no-win conclusion."""

        reasons: list[dict[str, str]] = []
        retry_stages: set[str] = set()

        def add(
            stage: str,
            reason: str,
            digest: str | None = None,
            *,
            code: str,
        ) -> None:
            item = {"stage": stage, "reason": reason, "code": code}
            if digest:
                item["canonical_digest"] = digest
            reasons.append(item)
            retry_stages.add(stage)

        if stage2.get("selection_exhausted", True) is not True:
            add(
                "stage2_sector_audit",
                "Stage 2 candidate selection was truncated before exhaustion",
                code="STAGE2_SELECTION_TRUNCATED",
            )
        for field, description in (
            (
                "canonicalization_errors",
                "Stage 2 candidates failed authoritative canonicalization",
            ),
            (
                "unsupported_candidates_skipped",
                "Stage 2 skipped unsupported candidates",
            ),
            ("malformed_records", "Stage 2 skipped malformed candidate records"),
        ):
            try:
                count = int(stage2.get(field, 0) or 0)
            except (TypeError, ValueError):
                count = 1
            if count:
                add(
                    "stage2_sector_audit",
                    f"{description}: {count}",
                    code=f"STAGE2_{field.upper()}",
                )
        for field in ("operational_errors", "certificate_operational_errors"):
            try:
                count = int(stage2.get(field, 0) or 0)
            except (TypeError, ValueError):
                count = 1
            if count:
                add(
                    "stage2_sector_audit",
                    f"Stage 2 reports {field}: {count}",
                    code=f"STAGE2_{field.upper()}",
                )

        if stage3.get("selection_exhausted", True) is not True:
            add(
                "stage3_direction_audit",
                "Stage 3 unresolved-candidate selection was truncated",
                code="STAGE3_SELECTION_TRUNCATED",
            )
        try:
            stage3_operational_errors = int(
                stage3.get("operational_errors", 0) or 0
            )
        except (TypeError, ValueError):
            stage3_operational_errors = 1
        if stage3_operational_errors:
            add(
                "stage3_direction_audit",
                f"Stage 3 reports operational_errors: "
                f"{stage3_operational_errors}",
                code="STAGE3_OPERATIONAL_ERRORS",
            )

        stage3_by_digest = {
            str(result.get("canonical_digest")): result
            for result in stage3.get("results", [])
            if isinstance(result, Mapping) and result.get("canonical_digest")
        }
        for result in stage2.get("results", []):
            if not isinstance(result, Mapping):
                continue
            digest = str(result.get("canonical_digest", ""))
            status = result.get("status")
            if status in {
                "THRESHOLD_PROVEN",
                "EXACT_PROVEN",
            } and cls._certificate_requires_retry(result):
                add(
                    "stage2_sector_audit",
                    "Stage 2 threshold proof has incomplete or unverified certificate",
                    digest,
                    code="STAGE2_CERTIFICATE_INCOMPLETE",
                )
            elif status == "UNRESOLVED":
                escalated = stage3_by_digest.get(digest)
                if escalated is None:
                    add(
                        "stage3_direction_audit",
                        "Stage 2 unresolved candidate lacks a Stage 3 result",
                        digest,
                        code="STAGE3_RESULT_MISSING",
                    )
                elif escalated.get("status") not in {
                    "REJECTED",
                    "THRESHOLD_PROVEN",
                    "EXACT_PROVEN",
                }:
                    add(
                        "stage3_direction_audit",
                        "Stage 3 did not reach a terminal proof result",
                        digest,
                        code="STAGE3_PROOF_INCOMPLETE",
                    )
            elif status == "ERROR":
                add(
                    "stage2_sector_audit",
                    "Stage 2 candidate audit ended in an operational error",
                    digest,
                    code="STAGE2_OPERATIONAL_ERROR",
                )

        for result in stage3.get("results", []):
            if not isinstance(result, Mapping):
                continue
            digest = str(result.get("canonical_digest", ""))
            if result.get("status") == "UNRESOLVED":
                add(
                    "stage3_direction_audit",
                    "Stage 3 logical-direction audit remains unresolved",
                    digest,
                    code="STAGE3_PROOF_INCOMPLETE",
                )
            elif result.get("status") == "ERROR":
                add(
                    "stage3_direction_audit",
                    "Stage 3 candidate audit ended in an operational error",
                    digest,
                    code="STAGE3_OPERATIONAL_ERROR",
                )
            elif (
                result.get("status") in {"THRESHOLD_PROVEN", "EXACT_PROVEN"}
                and cls._certificate_requires_retry(result)
            ):
                add(
                    "stage3_direction_audit",
                    "Stage 3 threshold proof has incomplete or unverified certificate",
                    digest,
                    code="STAGE3_CERTIFICATE_INCOMPLETE",
                )

        deduplicated: list[dict[str, str]] = []
        seen: set[str] = set()
        for reason in reasons:
            key = _canonical_sha256(reason)
            if key not in seen:
                seen.add(key)
                deduplicated.append(reason)
        return {
            "incomplete": bool(deduplicated),
            "reasons": deduplicated,
            "retry_stages": [
                stage for stage in STAGE_ORDER if stage in retry_stages
            ],
        }

    def _carry_paginated_input_incompleteness(
        self,
        stage2: Mapping[str, Any],
        incompleteness: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Carry global input diagnostics across acknowledged proof pages."""

        page = stage2.get("selection_page")
        if not isinstance(page, Mapping):
            return dict(incompleteness)
        binding = page.get("binding_sha256")
        if not isinstance(binding, str):
            return dict(incompleteness)

        pagination = self.state.setdefault("stage2_pagination", {})
        persisted: list[Mapping[str, Any]] = []
        if pagination.get("binding_sha256") == binding:
            raw_persisted = pagination.get("global_input_incompleteness", [])
            if isinstance(raw_persisted, list):
                persisted = [
                    reason
                    for reason in raw_persisted
                    if isinstance(reason, Mapping)
                    and reason.get("code")
                    in STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES
                ]
        else:
            pagination.pop("global_input_incompleteness", None)

        reasons = [
            dict(reason)
            for reason in incompleteness.get("reasons", [])
            if isinstance(reason, Mapping)
        ]
        seen = {_canonical_sha256(reason) for reason in reasons}
        for reason in persisted:
            item = dict(reason)
            key = _canonical_sha256(item)
            if key not in seen:
                seen.add(key)
                reasons.append(item)
        retry_stages = {
            str(stage)
            for stage in incompleteness.get("retry_stages", [])
            if stage in STAGE_ORDER
        }
        retry_stages.update(
            str(reason["stage"])
            for reason in reasons
            if reason.get("stage") in STAGE_ORDER
        )
        return {
            "incomplete": bool(reasons),
            "reasons": reasons,
            "retry_stages": [
                stage for stage in STAGE_ORDER if stage in retry_stages
            ],
        }

    def _mark_retryable_proof_stages(
        self,
        incompleteness: Mapping[str, Any],
    ) -> None:
        """Prevent incomplete proof stages from becoming reusable machine caches."""

        reasons = incompleteness.get("reasons", [])
        for stage in incompleteness.get("retry_stages", []):
            if stage not in {"stage2_sector_audit", "stage3_direction_audit"}:
                continue
            record = self.state["stages"][stage]
            stage_reasons = [
                dict(reason)
                for reason in reasons
                if isinstance(reason, Mapping) and reason.get("stage") == stage
            ]
            record["status"] = "INCOMPLETE"
            record["machine_status"] = "INCOMPLETE"
            record["incomplete_at"] = utc_now()
            record["incomplete_reasons"] = stage_reasons
        self._write_state()

    def _acknowledge_completed_stage2_page(
        self,
        state: Mapping[str, Any],
    ) -> bool:
        """Advance the durable cursor only after the current proof page closes."""

        if state.get("status") != "INCOMPLETE":
            return False
        result = state.get("result")
        if not isinstance(result, Mapping):
            return False
        if result.get("stage5_outcome") == "INCOMPLETE":
            # The current page owns a certificate replay checkpoint. Advancing
            # the Stage 2 cursor here would orphan that proof candidate.
            return False
        incompleteness = result.get("proof_incompleteness")
        if not isinstance(incompleteness, Mapping):
            return False
        reasons = incompleteness.get("reasons")
        if not isinstance(reasons, list) or not reasons:
            return False
        codes = [
            reason.get("code")
            for reason in reasons
            if isinstance(reason, Mapping)
        ]
        if (
            len(codes) != len(reasons)
            or "STAGE2_SELECTION_TRUNCATED" not in codes
            or any(
                code != "STAGE2_SELECTION_TRUNCATED"
                and code not in STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES
                for code in codes
            )
        ):
            return False

        summary = _read_json_object(self.paths.stage2_summary)
        page = summary.get("selection_page")
        # Old runs did not have a durable page. Returning INCOMPLETE is safer
        # than guessing a cursor and preserves backwards compatibility.
        if not isinstance(page, Mapping):
            return False
        self._ensure_solver_state_tree_safe()
        ledger = _read_json_object(self.paths.stage2_selection_ledger)
        if (
            ledger.get("schema_version")
            != STAGE2_SELECTION_LEDGER_SCHEMA_VERSION
            or ledger.get("gate") != STAGE2_SELECTION_LEDGER_GATE
            or ledger.get("binding_sha256") != page.get("binding_sha256")
            or ledger.get("pending") != dict(page)
            or ledger.get("cursor") != page.get("start_index")
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 selection ledger does not match its pending page",
                stage="stage2_sector_audit",
            )
        start_index = page.get("start_index")
        next_index = page.get("next_index")
        selected_digests = page.get("selected_digests")
        committed = ledger.get("committed_digests")
        completed_pages = ledger.get("completed_pages")
        if (
            isinstance(start_index, bool)
            or not isinstance(start_index, int)
            or isinstance(next_index, bool)
            or not isinstance(next_index, int)
            or not isinstance(selected_digests, list)
            or not isinstance(committed, list)
            or any(
                not isinstance(item, str) or not item
                for item in committed
            )
            or set(committed).intersection(selected_digests)
            or isinstance(completed_pages, bool)
            or not isinstance(completed_pages, int)
            or completed_pages < 0
        ):
            raise PipelineError(
                "NO_PAGINATION_PROGRESS",
                "Stage 2 pending page cannot advance its durable cursor",
                stage="stage2_sector_audit",
            )
        if next_index <= start_index or not selected_digests:
            self.state.setdefault("stage2_pagination", {}).update({
                "no_progress": True,
                "cursor": start_index,
                "pending_page_sha256": page.get("page_sha256"),
                "detected_at": utc_now(),
            })
            self._write_state()
            return False

        global_input_incompleteness = [
            dict(reason)
            for reason in reasons
            if (
                isinstance(reason, Mapping)
                and reason.get("code")
                in STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES
            )
        ]
        # Persist the fail-closed diagnostic before acknowledging the page. If
        # the ledger write is interrupted, replaying the same pending page can
        # only duplicate (and later deduplicate) this evidence.
        pagination = self.state.setdefault("stage2_pagination", {})
        pagination.update({
            "binding_sha256": page["binding_sha256"],
            "global_input_incompleteness": global_input_incompleteness,
            "pending_page_sha256": page["page_sha256"],
        })
        self._write_state()

        updated = dict(ledger)
        updated["cursor"] = next_index
        updated["committed_digests"] = [*committed, *selected_digests]
        updated["completed_pages"] = completed_pages + 1
        updated["pending"] = None
        updated["last_acknowledged_page_sha256"] = page["page_sha256"]
        updated["last_acknowledged_at"] = utc_now()
        atomic_write_json(self.paths.stage2_selection_ledger, updated)
        self._ensure_solver_state_tree_safe()

        pagination.update({
            "binding_sha256": page["binding_sha256"],
            "cursor": next_index,
            "completed_pages": updated["completed_pages"],
            "last_page_sha256": page["page_sha256"],
            "last_advanced_at": utc_now(),
        })
        self._write_state()
        return True

    def _merge_certificates(
        self,
        stage2: Mapping[str, Any],
        stage3: Mapping[str, Any],
        *,
        incompleteness: Mapping[str, Any] | None = None,
    ) -> dict[str, Any]:
        candidates = self._certificate_rows(stage2, "stage2_sector_audit")
        candidates.extend(self._certificate_rows(stage3, "stage3_direction_audit"))
        root = self.paths.solver_state.resolve()
        certificates: list[dict[str, Any]] = []
        entries: list[dict[str, Any]] = []
        seen: set[str] = set()
        for item in candidates:
            metadata = item["certificate"]
            path_value = metadata.get("certificate_path")
            verification_path_value = metadata.get("verification_path")
            if not isinstance(path_value, str) or not path_value:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "verified certificate result lacks certificate_path",
                    stage="stage4_certificate_merge",
                )
            if (
                not isinstance(verification_path_value, str)
                or not verification_path_value
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "verified certificate result lacks verification_path",
                    stage="stage4_certificate_merge",
                )
            path = _resolve_path(path_value, self.config.repo_dir)
            verification_path = _resolve_path(
                verification_path_value, self.config.repo_dir
            )
            for label, candidate_path in (
                ("certificate", path),
                ("verification sidecar", verification_path),
            ):
                try:
                    candidate_path.relative_to(root)
                except ValueError as exc:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{label} escapes pipeline solver state: {candidate_path}",
                        stage="stage4_certificate_merge",
                    ) from exc
            certificate = _read_json_object(path)
            certificate_sha = certificate.get("certificate_sha256")
            milp = certificate.get("milp")
            claim = certificate.get("claim")
            directions = milp.get("directions") if isinstance(milp, Mapping) else None
            try:
                exact = bool(
                    isinstance(milp, Mapping)
                    and isinstance(claim, Mapping)
                    and not isinstance(claim.get("k"), bool)
                    and isinstance(claim.get("k"), int)
                    and claim["k"] > 0
                    and not isinstance(claim.get("d"), bool)
                    and isinstance(claim.get("d"), int)
                    and claim["d"] > 0
                    and milp.get("exact") is True
                    and not isinstance(milp.get("completed_directions"), bool)
                    and not isinstance(milp.get("expected_directions"), bool)
                    and int(milp["expected_directions"]) > 0
                    and int(milp["completed_directions"])
                    == int(milp["expected_directions"])
                    and int(milp["expected_directions"]) == 2 * claim["k"]
                    and milp.get("distance") == claim["d"]
                    and isinstance(directions, list)
                    and len(directions) == 2 * claim["k"]
                    and all(isinstance(item, Mapping) for item in directions)
                )
            except (KeyError, TypeError, ValueError):
                exact = False
            if (
                not isinstance(certificate_sha, str)
                or not certificate_sha
                or certificate.get("passed") is not True
                or not exact
                or certificate_sha != _certificate_sha256(certificate)
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"certificate is not a passed exact artifact: {path}",
                    stage="stage4_certificate_merge",
                )
            metadata_sha = metadata.get("certificate_sha256")
            if metadata_sha is not None and metadata_sha != certificate_sha:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"certificate hash binding mismatch: {path}",
                    stage="stage4_certificate_merge",
                )
            verification_envelope = _read_json_object(verification_path)
            verification = verification_envelope.get("verification")
            payload_sha = _audit_json_sha256(certificate)
            known_answer_sha = _file_sha256(self.config.known_answer_artifact)
            if not (
                verification_envelope.get("schema_version") == 2
                and verification_envelope.get("kind")
                == "qldpc-certificate-verification-cache"
                and verification_envelope.get("canonical_digest")
                == item["canonical_digest"]
                and verification_envelope.get("known_answer_sha256") == known_answer_sha
                and verification_envelope.get("certificate_sha256") == certificate_sha
                and verification_envelope.get("certificate_payload_sha256")
                == payload_sha
                and isinstance(verification, Mapping)
                and verification.get("passed") is True
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"verification sidecar is not bound to certificate: {path}",
                    stage="stage4_certificate_merge",
                )
            if certificate_sha in seen:
                continue
            seen.add(certificate_sha)
            certificates.append(certificate)
            entries.append(
                {
                    "source_stage": item["source_stage"],
                    "canonical_digest": item["canonical_digest"],
                    "certificate_path": str(path),
                    "verification_path": str(verification_path),
                    "certificate_sha256": certificate_sha,
                    "certificate_payload_sha256": payload_sha,
                    "file_sha256": _file_sha256(path),
                    "verification_file_sha256": _file_sha256(verification_path),
                }
            )
        atomic_write_jsonl(self.paths.stage4_certificates, certificates)
        summary = {
            "schema_version": 1,
            "gate": "qcode-five-stage-certificate-merge",
            "generated_at": utc_now(),
            "passed": True,
            "verified_certificates": len(certificates),
            "certificate_output": str(self.paths.stage4_certificates),
            "entries": entries,
            "routing": (
                "STRICT_GATE"
                if certificates
                else (
                    "INCOMPLETE"
                    if incompleteness
                    and incompleteness.get("incomplete") is True
                    else "COMPLETED_NO_WIN"
                )
            ),
            "proof_incompleteness": (
                dict(incompleteness)
                if incompleteness
                and incompleteness.get("incomplete") is True
                else None
            ),
        }
        atomic_write_json(self.paths.stage4_summary, summary)
        return summary

    @staticmethod
    def _validate_stage4(summary_path: Path, claims_path: Path) -> dict[str, Any]:
        summary = _read_json_object(summary_path)
        if summary.get("gate") != "qcode-five-stage-certificate-merge":
            raise PipelineError("OUTPUT_INVALID", "invalid Stage 4 summary gate")
        count = summary.get("verified_certificates")
        if isinstance(count, bool) or not isinstance(count, int) or count < 0:
            raise PipelineError("OUTPUT_INVALID", "invalid Stage 4 certificate count")
        if not claims_path.is_file():
            raise PipelineError("OUTPUT_MISSING", "missing Stage 4 certificate JSONL")
        actual = sum(1 for line in claims_path.read_text().splitlines() if line.strip())
        if actual != count:
            raise PipelineError(
                "OUTPUT_INVALID",
                f"Stage 4 count mismatch: summary={count}, JSONL={actual}",
            )
        return summary

    def _strict_command(self) -> list[str]:
        return [
            self.config.python_executable,
            "-I",
            "-B",
            str(self.config.repo_dir / "scripts" / "finalize_challenge.py"),
            str(self.paths.stage4_certificates),
            "--known-answer-artifact",
            str(self.config.known_answer_artifact),
            "--known-answer-trust",
            str(self.config.known_answer_trust),
            "--known-answer-timeout-per-logical",
            str(
                self._scaled_strict_integer_timeout(
                    self.config.known_answer_timeout_per_logical
                )
            ),
            "--known-answer-total-timeout",
            str(
                self._scaled_strict_integer_timeout(
                    self.config.known_answer_total_timeout
                )
            ),
            "--verification-timeout-per-logical",
            str(
                self._scaled_strict_timeout(
                    self.config.verification_timeout_per_logical
                )
            ),
            "--verification-total-timeout",
            str(
                self._scaled_strict_timeout(
                    self.config.verification_total_timeout
                )
            ),
            "--verification-solver-workers",
            str(self.config.certificate_solver_workers),
            "--verification-state-dir",
            str(self.paths.solver_state / "strict-verification"),
            "--resume" if self.config.resume else "--no-resume",
            "--output",
            str(self.paths.stage5_gate),
        ]

    @staticmethod
    def _validate_final_gate(
        path: Path,
        certificates_path: Path,
    ) -> dict[str, Any]:
        value = _read_json_object(path)
        integrity = value.get("known_answer_integrity")
        evaluations = value.get("evaluations")
        summary = value.get("summary")
        if (
            value.get("gate") != "qldpc-challenge-final-batch"
            or not isinstance(integrity, Mapping)
            or integrity.get("mode") != "strict"
            or not isinstance(evaluations, list)
            or not evaluations
            or not isinstance(summary, Mapping)
        ):
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                "Stage 5 strict final gate is malformed",
                stage="stage5_strict_gate",
            )
        integrity_passed = integrity.get("passed") is True
        integrity_failures = integrity.get("failures")
        if integrity_passed:
            if integrity_failures != []:
                raise PipelineError(
                    "STRICT_GATE_REJECTED",
                    "passed Stage 5 known-answer integrity contains failures",
                    stage="stage5_strict_gate",
                )
        elif (
            integrity.get("passed") is not False
            or not isinstance(integrity_failures, list)
            or not integrity_failures
        ):
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                "failed Stage 5 known-answer integrity lacks failure evidence",
                stage="stage5_strict_gate",
            )
        try:
            accepted = summary["accepted"]
            rejected = summary["rejected"]
            incomplete = summary["incomplete"]
            total = summary["total"]
            if any(
                isinstance(item, bool) or not isinstance(item, int)
                for item in (accepted, rejected, incomplete, total)
            ):
                raise TypeError("summary counts must be integers")
        except (KeyError, TypeError, ValueError) as exc:
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                f"Stage 5 strict summary is invalid: {exc}",
                stage="stage5_strict_gate",
            ) from exc
        if (
            min(accepted, rejected, incomplete, total) < 0
            or total != len(evaluations)
            or accepted + rejected + incomplete != total
            or total == 0
        ):
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                "Stage 5 strict summary counts are inconsistent",
                stage="stage5_strict_gate",
            )
        outcome = value.get("outcome")
        expected_outcome = (
            "WIN"
            if accepted > 0 and integrity_passed
            else "INCOMPLETE"
            if incomplete > 0 or not integrity_passed
            else "NO_WIN"
        )
        if (
            outcome != expected_outcome
            or value.get("passed") is not (expected_outcome == "WIN")
            or (not integrity_passed and (accepted != 0 or incomplete != total))
        ):
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                "Stage 5 strict outcome is inconsistent with its evidence",
                stage="stage5_strict_gate",
            )
        try:
            certificates = [
                json.loads(line)
                for line in certificates_path.read_text().splitlines()
                if line.strip()
            ]
        except (OSError, json.JSONDecodeError) as exc:
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                f"Stage 5 certificate input is unavailable or invalid: {exc}",
                stage="stage5_strict_gate",
            ) from exc
        if not certificates or not all(
            isinstance(certificate, Mapping) for certificate in certificates
        ):
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                "Stage 5 certificate input must contain JSON objects",
                stage="stage5_strict_gate",
            )
        if len(certificates) != len(evaluations):
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                "Stage 5 evaluations do not cover every Stage 4 certificate",
                stage="stage5_strict_gate",
            )
        seen_hashes: set[str] = set()
        observed = {"ACCEPTED": 0, "REJECTED": 0, "INCOMPLETE": 0}
        for index, (certificate, evaluation) in enumerate(
            zip(certificates, evaluations, strict=True)
        ):
            assert isinstance(certificate, Mapping)
            assert isinstance(evaluation, Mapping)
            certificate_sha = certificate.get("certificate_sha256")
            result = evaluation.get("result")
            disposition = evaluation.get("disposition")
            source_index = evaluation.get("source_index")
            certificate_claim = certificate.get("claim")
            certificate_gate = certificate.get("final_gate")
            result_gate = (
                result.get("final_gate") if isinstance(result, Mapping) else None
            )
            checks = result.get("checks") if isinstance(result, Mapping) else None
            k = (
                certificate_claim.get("k")
                if isinstance(certificate_claim, Mapping)
                else None
            )
            d = (
                certificate_claim.get("d")
                if isinstance(certificate_claim, Mapping)
                else None
            )
            directions_verified = (
                result.get("directions_verified")
                if isinstance(result, Mapping)
                else None
            )
            directions_total = (
                result.get("directions_total") if isinstance(result, Mapping) else None
            )
            if (
                not isinstance(certificate_sha, str)
                or re.fullmatch(r"[0-9a-f]{64}", certificate_sha) is None
                or certificate_sha in seen_hashes
                or certificate_sha != _certificate_sha256(certificate)
                or certificate.get("passed") is not True
                or isinstance(source_index, bool)
                or not isinstance(source_index, int)
                or source_index != index
                or evaluation.get("certificate_sha256") != certificate_sha
                or evaluation.get("certificate_payload_sha256")
                != _canonical_sha256(certificate)
                or evaluation.get("claim") != certificate.get("claim")
                or not isinstance(result, Mapping)
                or disposition not in observed
            ):
                raise PipelineError(
                    "STRICT_GATE_REJECTED",
                    f"Stage 5 evaluation[{index}] is not bound to its certificate",
                    stage="stage5_strict_gate",
                )
            observed[str(disposition)] += 1
            failures = result.get("failures")
            if disposition == "INCOMPLETE":
                if (
                    result.get("passed") is not False
                    or result.get("replay_complete") is not False
                    or not isinstance(failures, list)
                    or not failures
                ):
                    raise PipelineError(
                        "STRICT_GATE_REJECTED",
                        f"Stage 5 evaluation[{index}] incomplete evidence is invalid",
                        stage="stage5_strict_gate",
                    )
            elif disposition == "REJECTED":
                if (
                    result.get("passed") is not False
                    or result.get("replay_complete") is not True
                    or not isinstance(failures, list)
                    or not failures
                ):
                    raise PipelineError(
                        "STRICT_GATE_REJECTED",
                        f"Stage 5 evaluation[{index}] rejection evidence is invalid",
                        stage="stage5_strict_gate",
                    )
            elif (
                result.get("passed") is not True
                or result.get("replay_complete") is not True
                or not isinstance(result.get("final_gate"), Mapping)
                or result["final_gate"].get("accepted") is not True
                or not isinstance(checks, Mapping)
                or not REQUIRED_STRICT_REPLAY_CHECKS.issubset(checks)
                or any(check is not True for check in checks.values())
                or failures != []
                or isinstance(k, bool)
                or not isinstance(k, int)
                or k <= 0
                or isinstance(d, bool)
                or not isinstance(d, int)
                or d <= 0
                or isinstance(result.get("distance"), bool)
                or result.get("distance") != d
                or isinstance(directions_verified, bool)
                or not isinstance(directions_verified, int)
                or directions_verified != 2 * k
                or isinstance(directions_total, bool)
                or not isinstance(directions_total, int)
                or directions_total != 2 * k
                or not isinstance(certificate_gate, Mapping)
                or not isinstance(result_gate, Mapping)
                or result_gate.get("accepted") is not True
                or _canonical_sha256(result_gate)
                != _canonical_sha256(certificate_gate)
            ):
                raise PipelineError(
                    "STRICT_GATE_REJECTED",
                    f"Stage 5 evaluation[{index}] accepted replay is invalid",
                    stage="stage5_strict_gate",
                )
            seen_hashes.add(certificate_sha)
        if (
            observed["ACCEPTED"] != accepted
            or observed["REJECTED"] != rejected
            or observed["INCOMPLETE"] != incomplete
        ):
            raise PipelineError(
                "STRICT_GATE_REJECTED",
                "Stage 5 dispositions do not match summary counts",
                stage="stage5_strict_gate",
            )
        return value

    def _proof_retry_base_config(self) -> dict[str, Any]:
        """Return the immutable retry binding; workers are never multiplied."""

        return {
            "stage2_top": self.config.stage2_top,
            "stage2_timeout": self.config.stage2_timeout,
            "stage2_candidate_workers": self.config.stage2_candidate_workers,
            "stage2_solver_workers": self.config.stage2_solver_workers,
            "stage3_top": self.config.stage3_top,
            "stage3_timeout": self.config.stage3_timeout,
            "stage3_candidate_workers": self.config.stage3_candidate_workers,
            "stage3_direction_workers": self.config.stage3_direction_workers,
            "stage3_exact": self.config.stage3_exact,
            "certificate_workers": self.config.certificate_workers,
            "certificate_solver_workers": self.config.certificate_solver_workers,
            "certificate_timeout_per_logical": (
                self.config.certificate_timeout_per_logical
            ),
            "certificate_total_timeout": self.config.certificate_total_timeout,
            "verification_timeout_per_logical": (
                self.config.verification_timeout_per_logical
            ),
            "verification_total_timeout": (
                self.config.verification_total_timeout
            ),
            "known_answer_timeout_per_logical": (
                self.config.known_answer_timeout_per_logical
            ),
            "known_answer_total_timeout": (
                self.config.known_answer_total_timeout
            ),
            "max_total_workers": self.config.max_total_workers,
            "max_attempts": self.config.proof_retry_max_attempts,
            "max_multiplier": self.config.proof_retry_max_multiplier,
            "campaign_total_timeout": (
                self.config.proof_retry_campaign_total_timeout
            ),
        }

    @staticmethod
    def _proof_retry_eligible(incompleteness: Mapping[str, Any]) -> bool:
        """Retry only solver/certificate liveness failures, not bad inputs."""

        retryable_codes = {
            "STAGE2_CERTIFICATE_INCOMPLETE",
            "STAGE2_OPERATIONAL_ERROR",
            "STAGE2_OPERATIONAL_ERRORS",
            "STAGE2_CERTIFICATE_OPERATIONAL_ERRORS",
            "STAGE3_RESULT_MISSING",
            "STAGE3_PROOF_INCOMPLETE",
            "STAGE3_OPERATIONAL_ERROR",
            "STAGE3_OPERATIONAL_ERRORS",
            "STAGE3_CERTIFICATE_INCOMPLETE",
            "STAGE5_STRICT_REPLAY_INCOMPLETE",
        }
        return any(
            isinstance(reason, Mapping)
            and reason.get("code") in retryable_codes
            for reason in incompleteness.get("reasons", [])
        )

    def _current_proof_retry_binding(self) -> dict[str, Any] | None:
        """Bind retries to exactly one durable page and current proof sources."""

        if not self.paths.stage2_summary.is_file():
            return None
        try:
            summary = _read_json_object(self.paths.stage2_summary)
        except PipelineError:
            return None
        if summary.get("gate") != "qldpc-proof-oriented-candidate-pool":
            return None
        page = summary.get("selection_page")
        selected_digests: list[str] = []
        if isinstance(page, Mapping):
            raw_digests = page.get("selected_digests")
            if not isinstance(raw_digests, list) or any(
                not isinstance(item, str) or not item for item in raw_digests
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 retry page has invalid selected_digests",
                    stage="stage2_sector_audit",
                )
            selected_digests = list(raw_digests)
            page_payload = {
                "binding_sha256": page.get("binding_sha256"),
                "start_index": page.get("start_index"),
                "next_index": page.get("next_index"),
                "selected_digests": selected_digests,
            }
            page_sha256 = _canonical_sha256(page_payload)
            if page.get("page_sha256") != page_sha256:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 retry page hash does not replay",
                    stage="stage2_sector_audit",
                )
            selection_binding = page.get("binding_sha256")
            if self.paths.stage2_selection_ledger.is_file():
                ledger = _read_json_object(
                    self.paths.stage2_selection_ledger
                )
                if (
                    ledger.get("schema_version")
                    != STAGE2_SELECTION_LEDGER_SCHEMA_VERSION
                    or ledger.get("gate") != STAGE2_SELECTION_LEDGER_GATE
                    or ledger.get("binding_sha256") != selection_binding
                ):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "proof retry selection ledger has an invalid binding",
                        stage="stage2_sector_audit",
                    )
                # A crash after page acknowledgement but before the pipeline
                # state update must start the new cursor at 1x.  It may not
                # spend an old page's prepared retry on a different page.
                if (
                    ledger.get("pending") != dict(page)
                    or ledger.get("cursor") != page.get("start_index")
                ):
                    return None
        else:
            for result in summary.get("results", []):
                if not isinstance(result, Mapping):
                    continue
                digest = result.get("canonical_digest")
                if isinstance(digest, str) and digest:
                    selected_digests.append(digest)
            selection_binding = None
            page_sha256 = _canonical_sha256(
                {
                    "legacy_page": True,
                    "selected_digests": selected_digests,
                    "stage2_inputs": self.state.get("stages", {})
                    .get("stage2_sector_audit", {})
                    .get("input_hashes", {}),
                }
            )
        if len(set(selected_digests)) != len(selected_digests):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 retry page repeats a canonical digest",
                stage="stage2_sector_audit",
            )
        source = self._audit_source_provenance()
        strict_source = self._strict_source_provenance()
        base_config = self._proof_retry_base_config()
        strict_inputs = _hash_paths(
            [
                self.paths.stage4_certificates,
                self.config.known_answer_artifact,
                self.config.known_answer_trust,
            ],
            require=False,
        )
        binding = {
            "page_sha256": page_sha256,
            "selection_binding_sha256": selection_binding,
            "selected_digests": selected_digests,
            "candidate_digests_sha256": _canonical_sha256(selected_digests),
            "source_fingerprint": source["source_fingerprint"],
            "controller_source_sha256": source["controller_source_sha256"],
            "known_code_registry_sha256": source[
                "known_code_registry_sha256"
            ],
            "strict_source_fingerprint": strict_source["source_fingerprint"],
            "strict_runner_sha256": strict_source["strict_runner_sha256"],
            "proof_runtime": source["proof_runtime"],
            "proof_interpreter": source["proof_interpreter"],
            "strict_inputs": strict_inputs,
            "proof_config_sha256": _canonical_sha256(base_config),
            "stage1_outputs_sha256": _canonical_sha256(
                self.state.get("stages", {})
                .get("stage1_search", {})
                .get("output_hashes", {})
            ),
        }
        return {
            **binding,
            "binding_sha256": _canonical_sha256(binding),
        }

    def _proof_progress_snapshot(self) -> dict[str, Any]:
        """Count durable sector/direction checkpoints without trusting results."""

        self._ensure_solver_state_tree_safe()
        roots = (
            self.paths.solver_state / "xor",
            self.paths.solver_state / "directions",
            self.paths.solver_state / "checkpoints",
            self.paths.solver_state / "strict-verification",
        )
        units: dict[str, dict[str, Any]] = {}
        for root in roots:
            if not root.is_dir():
                continue
            for path in sorted(root.glob("*.json")):
                try:
                    value = json.loads(path.read_text())
                except (OSError, UnicodeError, json.JSONDecodeError):
                    continue
                if not isinstance(value, Mapping):
                    continue
                candidates: list[int] = []
                for key in ("completed_directions", "completed_sectors"):
                    raw = value.get(key)
                    if (
                        isinstance(raw, int)
                        and not isinstance(raw, bool)
                        and raw >= 0
                    ):
                        candidates.append(raw)
                for key in ("directions", "sectors"):
                    raw = value.get(key)
                    if isinstance(raw, list):
                        candidates.append(len(raw))
                completed = max(candidates, default=0)
                if completed:
                    relative = path.relative_to(self.paths.solver_state).as_posix()
                    units[relative] = {
                        "completed_units": completed,
                        "sha256": _file_sha256(path),
                    }
        return {
            "completed_units": sum(
                int(item["completed_units"]) for item in units.values()
            ),
            "checkpoint_count": len(units),
            "checkpoints_sha256": _canonical_sha256(units),
            "units": units,
        }

    def _load_proof_retry_controller(self) -> dict[str, Any]:
        if not self.paths.proof_retry_controller.is_file():
            return {
                "schema_version": PROOF_RETRY_CONTROLLER_SCHEMA_VERSION,
                "gate": PROOF_RETRY_CONTROLLER_GATE,
                "created_at": utc_now(),
                "active": None,
                "history": [],
            }
        value = _read_json_object(self.paths.proof_retry_controller)
        if (
            value.get("schema_version")
            != PROOF_RETRY_CONTROLLER_SCHEMA_VERSION
            or value.get("gate") != PROOF_RETRY_CONTROLLER_GATE
            or not isinstance(value.get("history"), list)
            or (
                value.get("active") is not None
                and not isinstance(value.get("active"), Mapping)
            )
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                "invalid durable proof retry controller",
                stage="stage2_sector_audit",
            )
        active = value.get("active")
        if isinstance(active, Mapping):
            binding = active.get("binding")
            attempts = active.get("attempts")
            binding_sha256 = active.get("binding_sha256")
            if not isinstance(binding, Mapping):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "proof retry controller lacks its binding",
                    stage="stage2_sector_audit",
                )
            unsigned_binding = dict(binding)
            embedded_sha256 = unsigned_binding.pop("binding_sha256", None)
            if not (
                isinstance(binding_sha256, str)
                and embedded_sha256 == binding_sha256
                and _canonical_sha256(unsigned_binding) == binding_sha256
                and isinstance(attempts, list)
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "proof retry controller binding does not replay",
                    stage="stage2_sector_audit",
                )
            prepared_seen = False
            for index, attempt in enumerate(attempts, start=1):
                if (
                    not isinstance(attempt, Mapping)
                    or attempt.get("attempt") != index
                    or attempt.get("status")
                    not in {
                        "PREPARED",
                        "COMPLETED_INCOMPLETE",
                        "COMPLETED_WIN",
                        "COMPLETED_NO_WIN",
                        "FAILED",
                    }
                ):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "proof retry controller has invalid attempt history",
                        stage="stage2_sector_audit",
                    )
                multiplier = attempt.get("multiplier")
                if (
                    isinstance(multiplier, bool)
                    or not isinstance(multiplier, (int, float))
                    or not math.isfinite(float(multiplier))
                    or multiplier < 1
                    or prepared_seen
                ):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "proof retry controller has an invalid multiplier/order",
                        stage="stage2_sector_audit",
                    )
                prepared_seen = attempt.get("status") == "PREPARED"
                if prepared_seen and index != len(attempts):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "only the last proof retry attempt may be prepared",
                        stage="stage2_sector_audit",
                    )
        return value

    def _write_proof_retry_controller(
        self,
        controller: Mapping[str, Any],
    ) -> None:
        atomic_write_json(self.paths.proof_retry_controller, controller)
        self._ensure_solver_state_tree_safe()

    def _activate_proof_retry_binding(
        self,
        controller: dict[str, Any],
        binding: Mapping[str, Any],
    ) -> dict[str, Any]:
        active = controller.get("active")
        if (
            isinstance(active, Mapping)
            and active.get("binding_sha256") == binding.get("binding_sha256")
        ):
            return dict(active)
        if isinstance(active, Mapping):
            archived = dict(active)
            archived["archived_at"] = utc_now()
            if archived.get("status") == "ACTIVE":
                archived["status"] = "SUPERSEDED"
            controller.setdefault("history", []).append(archived)
            controller["history"] = controller["history"][-128:]
        active = {
            "binding": dict(binding),
            "binding_sha256": binding["binding_sha256"],
            "status": "ACTIVE",
            "started_at": utc_now(),
            "elapsed_seconds": 0.0,
            "attempts": [],
        }
        controller["active"] = active
        self._write_proof_retry_controller(controller)
        return active

    @staticmethod
    def _proof_progress_made(
        before: Mapping[str, Any],
        after: Mapping[str, Any],
    ) -> bool:
        before_units = before.get("units", {})
        after_units = after.get("units", {})
        if not isinstance(before_units, Mapping) or not isinstance(
            after_units, Mapping
        ):
            return False
        for path, raw_after in after_units.items():
            if not isinstance(raw_after, Mapping):
                continue
            raw_before = before_units.get(path, {})
            previous = (
                raw_before.get("completed_units", 0)
                if isinstance(raw_before, Mapping)
                else 0
            )
            current = raw_after.get("completed_units", 0)
            if (
                isinstance(previous, int)
                and isinstance(current, int)
                and current > previous
            ):
                return True
        return False

    def _adopt_initial_proof_attempt(
        self,
        controller: dict[str, Any],
        active: dict[str, Any],
        *,
        duration: float,
        incompleteness: Mapping[str, Any],
    ) -> None:
        progress = self._proof_progress_snapshot()
        empty_progress = {
            "completed_units": 0,
            "checkpoint_count": 0,
            "checkpoints_sha256": _canonical_sha256({}),
            "units": {},
        }
        attempts = active.setdefault("attempts", [])
        attempts.append(
            {
                "attempt": len(attempts) + 1,
                "multiplier": 1.0,
                "status": "COMPLETED_INCOMPLETE",
                "adopted_initial_attempt": True,
                "prepared_at": self.state.get("incomplete_at", utc_now()),
                "completed_at": utc_now(),
                "duration_seconds": max(0.0, float(duration)),
                "progress_before": empty_progress,
                "progress_after": progress,
                "made_progress": self._proof_progress_made(
                    empty_progress, progress
                ),
                "proof_incompleteness_sha256": _canonical_sha256(
                    incompleteness
                ),
            }
        )
        active["elapsed_seconds"] = float(
            active.get("elapsed_seconds", 0)
        ) + max(0.0, float(duration))
        controller["active"] = active
        self._write_proof_retry_controller(controller)

    def _proof_retry_decision(
        self,
        active: Mapping[str, Any],
    ) -> tuple[float | None, str | None]:
        attempts = active.get("attempts", [])
        if not isinstance(attempts, list) or not attempts:
            return 1.0, None
        if len(attempts) >= self.config.proof_retry_max_attempts:
            return None, "MAX_ATTEMPTS_REACHED"
        elapsed = active.get("elapsed_seconds", 0)
        if (
            not isinstance(elapsed, (int, float))
            or isinstance(elapsed, bool)
            or elapsed >= self.config.proof_retry_campaign_total_timeout
        ):
            return None, "CAMPAIGN_TOTAL_TIMEOUT_REACHED"
        latest = attempts[-1]
        if not isinstance(latest, Mapping):
            return None, "INVALID_ATTEMPT_HISTORY"
        if latest.get("status") == "PREPARED":
            multiplier = latest.get("multiplier")
            if isinstance(multiplier, (int, float)) and not isinstance(
                multiplier, bool
            ) and 1 <= float(multiplier) <= float(
                self.config.proof_retry_max_multiplier
            ):
                return float(multiplier), None
            return None, "INVALID_PREPARED_BUDGET"
        multiplier = float(latest.get("multiplier", 1))
        if latest.get("made_progress") is True:
            return multiplier, None
        maximum = float(self.config.proof_retry_max_multiplier)
        if multiplier >= maximum:
            return None, "NO_PROGRESS_AT_MAX_MULTIPLIER"
        return min(maximum, multiplier * 2), None

    def _prepare_proof_retry_attempt(
        self,
        controller: dict[str, Any],
        active: dict[str, Any],
        multiplier: float,
    ) -> dict[str, Any]:
        attempts = active.setdefault("attempts", [])
        if attempts and attempts[-1].get("status") == "PREPARED":
            attempt = attempts[-1]
        else:
            attempt = {
                "attempt": len(attempts) + 1,
                "multiplier": float(multiplier),
                "status": "PREPARED",
                "prepared_at": utc_now(),
                "execution_attempt_before": int(
                    self.state.get("execution_attempt", 0)
                ),
                "binding_sha256": active["binding_sha256"],
                "selected_digests": list(
                    active.get("binding", {}).get("selected_digests", [])
                ),
                "budget": {
                    "stage2_timeout": self.config.stage2_timeout * multiplier,
                    "stage3_timeout": self.config.stage3_timeout * multiplier,
                    "certificate_timeout_per_logical": (
                        self.config.certificate_timeout_per_logical * multiplier
                    ),
                    "certificate_total_timeout": (
                        self.config.certificate_total_timeout * multiplier
                    ),
                    "verification_timeout_per_logical": (
                        self.config.verification_timeout_per_logical * multiplier
                    ),
                    "verification_total_timeout": (
                        self.config.verification_total_timeout * multiplier
                    ),
                    "max_total_workers": self.config.max_total_workers,
                },
                "progress_before": self._proof_progress_snapshot(),
            }
            attempts.append(attempt)
            controller["active"] = active
            self._write_proof_retry_controller(controller)
        if attempt.get("backoff_completed_at") is None:
            self._sleeper(float(self.config.proof_retry_backoff_seconds))
            attempt["backoff_completed_at"] = utc_now()
            self._write_proof_retry_controller(controller)
        return attempt

    def _complete_prepared_proof_attempt(
        self,
        controller: dict[str, Any],
        active: dict[str, Any],
        *,
        status: str,
        duration: float,
        incompleteness: Mapping[str, Any] | None,
    ) -> None:
        attempts = active.get("attempts", [])
        if not attempts or attempts[-1].get("status") != "PREPARED":
            raise PipelineError(
                "OUTPUT_INVALID",
                "proof retry completion lacks its durable prepared attempt",
                stage="stage2_sector_audit",
            )
        attempt = attempts[-1]
        after = self._proof_progress_snapshot()
        before = attempt.get("progress_before", {})
        attempt.update(
            {
                "status": status,
                "completed_at": utc_now(),
                "duration_seconds": max(0.0, float(duration)),
                "progress_after": after,
                "made_progress": self._proof_progress_made(before, after),
                "execution_attempt_after": int(
                    self.state.get("execution_attempt", 0)
                ),
            }
        )
        if incompleteness is not None:
            attempt["proof_incompleteness_sha256"] = _canonical_sha256(
                incompleteness
            )
        active["elapsed_seconds"] = float(
            active.get("elapsed_seconds", 0)
        ) + max(0.0, float(duration))
        if status in {"COMPLETED_WIN", "COMPLETED_NO_WIN"}:
            active["status"] = status
            active["finished_at"] = utc_now()
        controller["active"] = active
        self._write_proof_retry_controller(controller)

    def _mark_proof_retry_capped(
        self,
        controller: dict[str, Any],
        active: dict[str, Any],
        reason: str,
    ) -> dict[str, Any]:
        active.update(
            {
                "status": "CAPPED",
                "cap_reason": reason,
                "capped_at": utc_now(),
                "resume_required": True,
            }
        )
        controller["active"] = active
        self._write_proof_retry_controller(controller)
        public = {
            "binding_sha256": active["binding_sha256"],
            "status": "CAPPED",
            "cap_reason": reason,
            "attempts": len(active.get("attempts", [])),
            "elapsed_seconds": active.get("elapsed_seconds", 0),
            "resume_required": True,
            "controller_path": str(self.paths.proof_retry_controller),
        }
        self.state["proof_retry"] = public
        self.state.setdefault("stage2_pagination", {}).update(
            {
                "resume_required": True,
                "proof_retry_cap_reason": reason,
            }
        )
        result = self.state.get("result")
        if isinstance(result, dict):
            result["proof_retry"] = public
        self._write_state()
        return self.state

    def _record_failure(self, error: PipelineError) -> dict[str, Any]:
        stage = error.stage or self.state.get("active_stage")
        if stage in self.state.get("stages", {}):
            record = self.state["stages"][stage]
            record["status"] = "FAILED"
            if record.get("machine_status") == "RUNNING":
                record["machine_status"] = "FAILED"
            record["finished_at"] = utc_now()
            record["failure"] = {
                "classification": error.classification,
                "message": str(error),
                "exit_code": error.exit_code,
            }
        self.state["status"] = "FAILED"
        self.state["active_stage"] = None
        self.state["failure"] = {
            "classification": error.classification,
            "stage": stage,
            "message": str(error),
            "exit_code": error.exit_code,
            "timestamp": utc_now(),
        }
        self._write_state()
        return self.state

    def _run_locked(self) -> dict[str, Any]:
        self._load_or_initialize_state()
        previous_status = self.state.get("status")
        previous_result = self.state.pop("result", None)
        previous_completed_at = self.state.pop("completed_at", None)
        previous_incomplete_at = self.state.pop("incomplete_at", None)
        if (
            previous_result is not None
            or previous_completed_at is not None
            or previous_incomplete_at is not None
        ):
            self.state.setdefault("result_history", []).append(
                {
                    "status": previous_status,
                    "completed_at": previous_completed_at,
                    "incomplete_at": previous_incomplete_at,
                    "result": previous_result,
                    "archived_at": utc_now(),
                }
            )
        self.state["execution_attempt"] = (
            int(self.state.get("execution_attempt", 0)) + 1
        )
        self.state["status"] = "RUNNING"
        self.state.pop("failure", None)
        self._write_state()
        try:
            candidates = self._stage1_inputs()
            controller_source = self.config.repo_dir / "humanize" / "pipeline.py"
            known_code_registry = (
                self.config.repo_dir / "results" / "known_code_registry.json"
            )
            strict_known_answer_runner = (
                self.config.repo_dir / "tests" / "verify_known_answer_gate.py"
            )
            # Fail before proof stages when any current proof/release source is
            # missing, linked, or otherwise unsafe. Each live stage repeats
            # this replay after its machine work to close the source TOCTOU.
            self._audit_source_provenance()
            self._strict_source_provenance()

            stage2_command = self._stage2_command(candidates)
            stage2_static_config = {
                "top": self.config.stage2_top,
                "timeout": self._scaled_proof_timeout(
                    self.config.stage2_timeout
                ),
                "proof_budget_multiplier": self._proof_budget_multiplier,
                "candidate_workers": self.config.stage2_candidate_workers,
                "solver_workers": self.config.stage2_solver_workers,
                "certificate_workers": self.config.certificate_workers,
                "certificate_solver_workers": (
                    self.config.certificate_solver_workers
                ),
                "certificate_timeouts": [
                    self._scaled_proof_timeout(
                        self.config.certificate_timeout_per_logical
                    ),
                    self._scaled_proof_timeout(
                        self.config.certificate_total_timeout
                    ),
                    self._scaled_proof_timeout(
                        self.config.verification_timeout_per_logical
                    ),
                    self._scaled_proof_timeout(
                        self.config.verification_total_timeout
                    ),
                ],
                "max_total_workers": self.config.max_total_workers,
                "resume": self.config.resume,
            }

            def current_stage2_config() -> dict[str, Any]:
                return {
                    **self._audit_source_provenance(),
                    **stage2_static_config,
                }

            stage2_config = current_stage2_config()
            stage2 = self._execute_stage(
                "stage2_sector_audit",
                command=stage2_command,
                stage_config=stage2_config,
                stage_config_revalidator=current_stage2_config,
                inputs=[
                    *candidates,
                    self.config.repo_dir / "scripts" / "audit_candidate_pool.py",
                    self.config.known_answer_artifact,
                    known_code_registry,
                ],
                outputs=[self.paths.stage2_ranked, self.paths.stage2_summary],
                machine=lambda: self._run_command(
                    "stage2_sector_audit",
                    stage2_command,
                    self.paths.logs / "stage2-sector-audit.log",
                ),
                validator=lambda: self._validate_pool_summary(
                    self.paths.stage2_summary,
                    self.paths.stage2_ranked,
                    "qldpc-proof-oriented-candidate-pool",
                ),
                recoverable_exit_codes=RECOVERABLE_PROOF_EXIT_CODES,
                nonzero_validator=lambda: self._validate_recoverable_pool_summary(
                    self.paths.stage2_summary,
                    self.paths.stage2_ranked,
                    "qldpc-proof-oriented-candidate-pool",
                ),
            )

            has_unresolved = any(
                isinstance(result, Mapping) and result.get("status") == "UNRESOLVED"
                for result in stage2.get("results", [])
            )
            if has_unresolved:
                stage3_command = self._stage3_command()
                stage3_inputs = [
                    self.paths.stage2_ranked,
                    self.config.repo_dir / "scripts" / "audit_direction_pool.py",
                    self.config.known_answer_artifact,
                    known_code_registry,
                ]
                stage3_machine = lambda: self._run_command(
                    "stage3_direction_audit",
                    stage3_command,
                    self.paths.logs / "stage3-direction-audit.log",
                )
                stage3_machine_status = "COMPLETED"
            else:
                stage3_command = ["internal:skip-stage3-no-unresolved"]
                stage3_inputs = [self.paths.stage2_ranked, self.paths.stage2_summary]
                stage3_machine = lambda: self._write_skipped_stage3(stage2)
                stage3_machine_status = "SKIPPED"
            stage3_static_config = {
                "routing": "audit" if has_unresolved else "skip-no-unresolved",
                "top": self.config.stage3_top,
                "timeout": self._scaled_proof_timeout(
                    self.config.stage3_timeout
                ),
                "proof_budget_multiplier": self._proof_budget_multiplier,
                "candidate_workers": self.config.stage3_candidate_workers,
                "direction_workers": self.config.stage3_direction_workers,
                "exact": self.config.stage3_exact,
                "certificate_workers": self.config.certificate_workers,
                "certificate_solver_workers": (
                    self.config.certificate_solver_workers
                ),
                "certificate_timeouts": [
                    self._scaled_proof_timeout(
                        self.config.certificate_timeout_per_logical
                    ),
                    self._scaled_proof_timeout(
                        self.config.certificate_total_timeout
                    ),
                    self._scaled_proof_timeout(
                        self.config.verification_timeout_per_logical
                    ),
                    self._scaled_proof_timeout(
                        self.config.verification_total_timeout
                    ),
                ],
                "max_total_workers": self.config.max_total_workers,
                "resume": self.config.resume,
            }

            def current_stage3_config() -> dict[str, Any]:
                return {
                    **self._audit_source_provenance(),
                    **stage3_static_config,
                }

            stage3_config = current_stage3_config()
            stage3 = self._execute_stage(
                "stage3_direction_audit",
                command=stage3_command,
                stage_config=stage3_config,
                stage_config_revalidator=current_stage3_config,
                inputs=stage3_inputs,
                outputs=[
                    self.paths.stage3_ranked,
                    self.paths.stage3_summary,
                    self.paths.stage3_thresholds,
                ],
                machine=stage3_machine,
                validator=lambda: self._validate_pool_summary(
                    self.paths.stage3_summary,
                    self.paths.stage3_ranked,
                    "qldpc-direction-candidate-pool",
                ),
                recoverable_exit_codes=RECOVERABLE_PROOF_EXIT_CODES,
                nonzero_validator=lambda: self._validate_recoverable_pool_summary(
                    self.paths.stage3_summary,
                    self.paths.stage3_ranked,
                    "qldpc-direction-candidate-pool",
                ),
                machine_status=stage3_machine_status,
            )

            proof_incompleteness = self._proof_incompleteness(stage2, stage3)
            proof_incompleteness = self._carry_paginated_input_incompleteness(
                stage2,
                proof_incompleteness,
            )
            controller_source_sha256 = self._source_file_sha256(
                controller_source,
                label="pipeline controller source",
            )
            stage4_command = ["internal:merge-verified-certificates"]
            stage4 = self._execute_stage(
                "stage4_certificate_merge",
                command=stage4_command,
                stage_config={
                    "controller_source_sha256": controller_source_sha256,
                    "require_build_and_independent_verification": True,
                    "verification_sidecar_schema": 2,
                    "proof_completion_policy": 1,
                },
                inputs=[
                    self.paths.stage2_summary,
                    self.paths.stage3_summary,
                    self.config.known_answer_artifact,
                    controller_source,
                ],
                outputs=[
                    self.paths.stage4_certificates,
                    self.paths.stage4_summary,
                ],
                machine=lambda: (
                    (
                        self._merge_certificates(
                            stage2,
                            stage3,
                            incompleteness=proof_incompleteness,
                        )
                        is not None
                    )
                    - 1
                ),
                validator=lambda: self._validate_stage4(
                    self.paths.stage4_summary,
                    self.paths.stage4_certificates,
                ),
            )

            certificate_count = int(stage4["verified_certificates"])
            stage5_outcome: str | None = None
            if certificate_count:
                strict_command = self._strict_command()
                stage5_static_config = {
                    "mode": "strict",
                    "known_answer_timeout_per_logical": (
                        self._scaled_strict_integer_timeout(
                            self.config.known_answer_timeout_per_logical
                        )
                    ),
                    "known_answer_total_timeout": (
                        self._scaled_strict_integer_timeout(
                            self.config.known_answer_total_timeout
                        )
                    ),
                    "verification_timeout_per_logical": (
                        self._scaled_strict_timeout(
                            self.config.verification_timeout_per_logical
                        )
                    ),
                    "verification_total_timeout": (
                        self._scaled_strict_timeout(
                            self.config.verification_total_timeout
                        )
                    ),
                    "verification_solver_workers": (
                        self.config.certificate_solver_workers
                    ),
                }
                if float(self._proof_budget_multiplier) != 1.0:
                    stage5_static_config["proof_budget_multiplier"] = float(
                        self._proof_budget_multiplier
                    )

                def current_stage5_config() -> dict[str, Any]:
                    return {
                        **self._strict_source_provenance(),
                        **stage5_static_config,
                    }

                stage5_config = current_stage5_config()
                stage5 = self._execute_stage(
                    "stage5_strict_gate",
                    command=strict_command,
                    stage_config=stage5_config,
                    stage_config_revalidator=current_stage5_config,
                    inputs=[
                        self.paths.stage4_certificates,
                        self.config.repo_dir / "scripts" / "finalize_challenge.py",
                        strict_known_answer_runner,
                        self.config.known_answer_artifact,
                        self.config.known_answer_trust,
                        known_code_registry,
                    ],
                    outputs=[self.paths.stage5_gate],
                    machine=lambda: self._run_command(
                        "stage5_strict_gate",
                        strict_command,
                        self.paths.logs / "stage5-strict-gate.log",
                    ),
                    validator=lambda: self._validate_final_gate(
                        self.paths.stage5_gate,
                        self.paths.stage4_certificates,
                    ),
                )
                stage5_outcome = stage5["outcome"]
                if stage5_outcome == "WIN":
                    terminal_status = "COMPLETED_WIN"
                elif stage5_outcome == "INCOMPLETE":
                    terminal_status = "INCOMPLETE"
                    stage5_reason = {
                        "stage": "stage5_strict_gate",
                        "code": "STAGE5_STRICT_REPLAY_INCOMPLETE",
                        "message": (
                            "No certificate passed and at least one strict "
                            "certificate replay remains incomplete"
                        ),
                    }
                    existing_reasons = [
                        dict(reason)
                        for reason in proof_incompleteness.get("reasons", [])
                        if isinstance(reason, Mapping)
                    ]
                    if not any(
                        reason.get("code") == stage5_reason["code"]
                        for reason in existing_reasons
                    ):
                        existing_reasons.append(stage5_reason)
                    retry_stages = {
                        str(stage)
                        for stage in proof_incompleteness.get(
                            "retry_stages", []
                        )
                        if stage in STAGE_ORDER
                    }
                    retry_stages.add("stage5_strict_gate")
                    proof_incompleteness = {
                        "incomplete": True,
                        "reasons": existing_reasons,
                        "retry_stages": [
                            stage
                            for stage in STAGE_ORDER
                            if stage in retry_stages
                        ],
                    }
                    record = self.state["stages"]["stage5_strict_gate"]
                    record["status"] = "INCOMPLETE"
                    record["machine_status"] = "INCOMPLETE"
                    record["incomplete_at"] = utc_now()
                    record["incomplete_reasons"] = [stage5_reason]
                    self._mark_retryable_proof_stages(proof_incompleteness)
                elif proof_incompleteness["incomplete"] is True:
                    terminal_status = "INCOMPLETE"
                    self._mark_retryable_proof_stages(proof_incompleteness)
                else:
                    terminal_status = "COMPLETED_NO_WIN"
            elif proof_incompleteness["incomplete"] is True:
                incomplete = {
                    "schema_version": 1,
                    "gate": "qcode-five-stage-terminal",
                    "generated_at": utc_now(),
                    "status": "INCOMPLETE",
                    "reason": (
                        "Proof coverage is not exhaustive and no independently "
                        "verified exact certificate is currently available"
                    ),
                    "proof_incompleteness": proof_incompleteness,
                }
                incomplete_command = ["internal:incomplete-proof-work"]
                self._execute_stage(
                    "stage5_strict_gate",
                    command=incomplete_command,
                    stage_config={
                        "routing": "incomplete-proof-work",
                        "proof_completion_policy": 1,
                    },
                    inputs=[self.paths.stage4_summary],
                    outputs=[self.paths.stage5_incomplete],
                    machine=lambda: (
                        atomic_write_json(
                            self.paths.stage5_incomplete,
                            incomplete,
                        )
                        or 0
                    ),
                    validator=lambda: _read_json_object(
                        self.paths.stage5_incomplete
                    ),
                    machine_status="SKIPPED",
                )
                terminal_status = "INCOMPLETE"
                self._mark_retryable_proof_stages(proof_incompleteness)
            else:
                no_win = {
                    "schema_version": 1,
                    "gate": "qcode-five-stage-terminal",
                    "generated_at": utc_now(),
                    "status": "COMPLETED_NO_WIN",
                    "reason": (
                        "Stages 2-4 produced no certificate that passed both "
                        "exact construction and independent verification"
                    ),
                }
                no_win_command = ["internal:complete-without-certified-win"]
                self._execute_stage(
                    "stage5_strict_gate",
                    command=no_win_command,
                    stage_config={"routing": "no-verified-certificate"},
                    inputs=[self.paths.stage4_summary],
                    outputs=[self.paths.stage5_no_win],
                    machine=lambda: (
                        atomic_write_json(self.paths.stage5_no_win, no_win) or 0
                    ),
                    validator=lambda: _read_json_object(self.paths.stage5_no_win),
                    machine_status="SKIPPED",
                )
                terminal_status = "COMPLETED_NO_WIN"

            self.state["status"] = terminal_status
            self.state["active_stage"] = None
            if terminal_status in TERMINAL_STATUSES:
                self.state["completed_at"] = utc_now()
                self.state.pop("incomplete_at", None)
            else:
                self.state["incomplete_at"] = utc_now()
                self.state.pop("completed_at", None)
            self.state["result"] = {
                "verified_certificates": certificate_count,
                "stage4_summary": str(self.paths.stage4_summary),
                "strict_gate": (
                    str(self.paths.stage5_gate) if certificate_count else None
                ),
                "stage5_outcome": stage5_outcome,
                "incomplete": (
                    (
                        str(self.paths.stage5_gate)
                        if certificate_count
                        else str(self.paths.stage5_incomplete)
                    )
                    if terminal_status == "INCOMPLETE"
                    else None
                ),
                "proof_incompleteness": (
                    proof_incompleteness
                    if proof_incompleteness["incomplete"] is True
                    else None
                ),
            }
            self._write_state()
            return self.state
        except PipelineError as exc:
            return self._record_failure(exc)
        except KeyboardInterrupt:
            self._record_failure(
                PipelineError(
                    "INTERRUPTED",
                    "pipeline interrupted",
                    stage=self.state.get("active_stage"),
                )
            )
            raise
        except Exception as exc:
            return self._record_failure(
                PipelineError(
                    "INTERNAL_ERROR",
                    f"{type(exc).__name__}: {exc}",
                    stage=self.state.get("active_stage"),
                )
            )

    def run(self) -> dict[str, Any]:
        """Run synchronously, advancing terminal proof pages under one lock."""

        with self._exclusive_lock():
            # max_attempts=1 is the explicit compatibility/diagnostic mode:
            # one proof pass per invocation and no in-process retry sleep.
            if self.config.proof_retry_max_attempts == 1:
                state: dict[str, Any] = {}
                for automatic_pass in range(
                    1, MAX_AUTOMATIC_PROOF_PASSES + 1
                ):
                    state = self._run_locked()
                    if state.get("status") != "INCOMPLETE":
                        return state
                    try:
                        advanced = self._acknowledge_completed_stage2_page(
                            state
                        )
                    except PipelineError as exc:
                        return self._record_failure(exc)
                    if not advanced:
                        return state
                    self.state.setdefault("stage2_pagination", {})[
                        "automatic_passes"
                    ] = automatic_pass
                    self._write_state()
                self.state.setdefault("stage2_pagination", {}).update(
                    {
                        "automatic_pass_limit": (
                            MAX_AUTOMATIC_PROOF_PASSES
                        ),
                        "resume_required": True,
                        "limit_reached_at": utc_now(),
                    }
                )
                self._write_state()
                return self.state

            # Load once before selecting a recovered PREPARED retry.  Each
            # _run_locked call reloads again before executing its stage state
            # machine, so a killed process can resume the same prepared budget.
            self._load_or_initialize_state()
            controller = self._load_proof_retry_controller()
            force_fresh_page = False
            state: dict[str, Any] = {}
            for automatic_pass in range(1, MAX_AUTOMATIC_PROOF_PASSES + 1):
                active: dict[str, Any] | None = None
                prepared: dict[str, Any] | None = None
                multiplier = 1.0
                binding = (
                    None
                    if force_fresh_page
                    else self._current_proof_retry_binding()
                )
                force_fresh_page = False
                raw_active = controller.get("active")
                if (
                    isinstance(binding, Mapping)
                    and isinstance(raw_active, Mapping)
                    and raw_active.get("binding_sha256")
                    == binding.get("binding_sha256")
                ):
                    active = dict(raw_active)
                    attempts = active.get("attempts", [])
                    latest = (
                        attempts[-1]
                        if isinstance(attempts, list) and attempts
                        else None
                    )
                    if active.get("status") == "CAPPED":
                        return self._mark_proof_retry_capped(
                            controller,
                            active,
                            str(
                                active.get(
                                    "cap_reason",
                                    "RETRY_CONTROLLER_ALREADY_CAPPED",
                                )
                            ),
                        )
                    should_resume_prepared = bool(
                        isinstance(latest, Mapping)
                        and latest.get("status") == "PREPARED"
                    )
                    current_result = self.state.get("result")
                    current_incompleteness = (
                        current_result.get("proof_incompleteness")
                        if isinstance(current_result, Mapping)
                        else None
                    )
                    should_schedule = bool(
                        self.state.get("status") == "INCOMPLETE"
                        and active.get("status") == "ACTIVE"
                        and isinstance(current_incompleteness, Mapping)
                        and self._proof_retry_eligible(
                            current_incompleteness
                        )
                    )
                    if should_resume_prepared or should_schedule:
                        multiplier, cap_reason = self._proof_retry_decision(
                            active
                        )
                        if multiplier is None:
                            return self._mark_proof_retry_capped(
                                controller,
                                active,
                                cap_reason or "RETRY_BUDGET_EXHAUSTED",
                            )
                        prepared = self._prepare_proof_retry_attempt(
                            controller,
                            active,
                            multiplier,
                        )

                self._proof_budget_multiplier = multiplier
                started = self._monotonic()
                try:
                    state = self._run_locked()
                finally:
                    duration = max(0.0, self._monotonic() - started)
                    self._proof_budget_multiplier = 1.0

                incompleteness: Mapping[str, Any] | None = None
                result = state.get("result")
                if isinstance(result, Mapping) and isinstance(
                    result.get("proof_incompleteness"), Mapping
                ):
                    incompleteness = result["proof_incompleteness"]
                if prepared is not None and active is not None:
                    completion_status = {
                        "COMPLETED_WIN": "COMPLETED_WIN",
                        "COMPLETED_NO_WIN": "COMPLETED_NO_WIN",
                        "INCOMPLETE": "COMPLETED_INCOMPLETE",
                    }.get(str(state.get("status")), "FAILED")
                    self._complete_prepared_proof_attempt(
                        controller,
                        active,
                        status=completion_status,
                        duration=duration,
                        incompleteness=incompleteness,
                    )
                if state.get("status") != "INCOMPLETE":
                    return state
                try:
                    advanced = self._acknowledge_completed_stage2_page(state)
                except PipelineError as exc:
                    return self._record_failure(exc)
                if advanced:
                    if active is not None:
                        active["status"] = "PAGE_COMPLETED"
                        active["finished_at"] = utc_now()
                        controller["active"] = active
                        self._write_proof_retry_controller(controller)
                    force_fresh_page = True
                    self.state.setdefault("stage2_pagination", {})[
                        "automatic_passes"
                    ] = automatic_pass
                    self._write_state()
                    continue

                binding = self._current_proof_retry_binding()
                if (
                    binding is None
                    or incompleteness is None
                    or not self._proof_retry_eligible(incompleteness)
                ):
                    return state
                active = self._activate_proof_retry_binding(
                    controller, binding
                )
                # The first 1x pass creates the page. Adopt it into the retry
                # ledger only after its complete INCOMPLETE artifact exists.
                if prepared is None:
                    self._adopt_initial_proof_attempt(
                        controller,
                        active,
                        duration=duration,
                        incompleteness=incompleteness,
                    )
                next_multiplier, cap_reason = self._proof_retry_decision(active)
                if next_multiplier is None:
                    return self._mark_proof_retry_capped(
                        controller,
                        active,
                        cap_reason or "RETRY_BUDGET_EXHAUSTED",
                    )
                self.state.setdefault("stage2_pagination", {})[
                    "automatic_passes"
                ] = automatic_pass
                self._write_state()

            active = controller.get("active")
            if isinstance(active, Mapping):
                return self._mark_proof_retry_capped(
                    controller,
                    dict(active),
                    "AUTOMATIC_PASS_LIMIT_REACHED",
                )
            self.state.setdefault("stage2_pagination", {}).update(
                {
                    "automatic_pass_limit": MAX_AUTOMATIC_PROOF_PASSES,
                    "resume_required": True,
                    "limit_reached_at": utc_now(),
                }
            )
            self._write_state()
            return self.state


def run_pipeline(
    config: PipelineConfig,
    *,
    command_runner: CommandRunner = default_command_runner,
    flow_factory: FlowFactory = HumanizeFlow,
    reviewer: StageReviewer | Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Library entry point used by Archon and the standalone CLI."""

    return FiveStagePipeline(
        config,
        command_runner=command_runner,
        flow_factory=flow_factory,
        reviewer=reviewer,
    ).run()
