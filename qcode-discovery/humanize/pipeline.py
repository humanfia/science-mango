"""Deterministic, resumable orchestration for the qcode five-stage campaign.

The controller deliberately keeps mathematical routing separate from Humanize
reviews.  Reviews are mandatory by default, but are advisory: only machine
artifacts decide whether a candidate advances to a certificate or the strict
terminal gate.
"""

from __future__ import annotations

import copy
import fcntl
import hashlib
import importlib.util
import inspect
import json
import marshal
import math
import os
import re
import signal
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

from evaluation.failure_disposition import (
    CERTIFICATE_CACHE_SCHEMA_VERSION,
    EVIDENCE_CONTRADICTION,
    INCOMPLETE as FAILURE_INCOMPLETE,
    terminal_candidate_rejection,
    validate_failure_disposition,
)
from evaluation.geometry import candidate_geometry
from evaluation.process_hard_wall import (
    linux_process_start_time,
    positive_wall_timeout,
    process_group_alive,
)
from evaluation.proof_runtime import (
    RuntimeProbeError,
    probe_python_runtime,
    proof_runtime_fingerprint,
    validate_proof_runtime_fingerprint,
)
from evaluation.selection_ledger import (
    SELECTION_LEDGER_GATE as SHARED_SELECTION_LEDGER_GATE,
    SELECTION_LEDGER_SCHEMA_VERSION as SHARED_SELECTION_LEDGER_SCHEMA_VERSION,
    acknowledge_selection_page,
    canonical_sha256 as selection_canonical_sha256,
    is_sha256 as is_selection_sha256,
    new_selection_ledger,
    seal_selection_ledger,
    validate_scan_evidence,
    validate_selection_ledger,
    validate_selection_page,
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
from .reviewer import REVIEW_SCHEMA, CodexReviewer, validate_review
from .state import RunStore

PIPELINE_SCHEMA_VERSION = 1
REVIEW_PROMPT_VERSION = 2
NEGATIVE_FEEDBACK_EPOCH_SCHEMA_VERSION = 1
NEGATIVE_FEEDBACK_STARTUP_KIND = (
    "qcode-pipeline-stage1-negative-feedback-startup"
)
NEGATIVE_FEEDBACK_CONSUMED_KIND = (
    "qcode-pipeline-stage1-negative-feedback-consumed"
)
NEGATIVE_FEEDBACK_PENDING_KIND = (
    "qcode-pipeline-negative-feedback-pending"
)
NEGATIVE_FEEDBACK_PREPARED_KIND = (
    "qcode-pipeline-stage1-negative-feedback-prepared"
)
STAGE2_SELECTION_LEDGER_SCHEMA_VERSION = (
    SHARED_SELECTION_LEDGER_SCHEMA_VERSION
)
STAGE2_SELECTION_LEDGER_GATE = SHARED_SELECTION_LEDGER_GATE
PROOF_RETRY_CONTROLLER_SCHEMA_VERSION = 1
PROOF_RETRY_CONTROLLER_GATE = "qldpc-proof-retry-controller"
STAGE2_DEFERRED_PAGE_SCHEMA_VERSION = 1
STAGE2_DEFERRED_PAGE_GATE = "qldpc-stage2-deferred-proof-page"
STAGE2_DEFERRED_PAGE_CODE = "STAGE2_DEFERRED_PROOF_PAGE"
STAGE2_STRUCTURAL_UNRESOLVED_CODE = (
    "STAGE2_STRUCTURAL_UNRESOLVED_CANDIDATES"
)
STAGE3_INELIGIBLE_RESULT_CODE = "STAGE3_INELIGIBLE_RESULT"
STAGE3_BOUND_INSUFFICIENT_RESULT_CODE = (
    "STAGE3_BOUND_INSUFFICIENT_RESULT"
)
STAGE3_EXACTNESS_GAP_RESULT_CODE = "STAGE3_EXACTNESS_GAP_RESULT"
STAGE2_LEDGER_GENERATION_GATE = "qldpc-stage2-ledger-generation"
RECOVERABLE_PROOF_EXIT_CODES = frozenset({2})
# PollSelector and several platform wait primitives store milliseconds in a
# signed C integer.  Keep every individual communicate wait comfortably below
# that limit while the monotonic deadline retains the full stage budget.
SUBPROCESS_COMMUNICATE_MAX_SLICE_S = 60.0
STAGE3_BACKENDS = frozenset({
    "legacy-directions",
    "sat-sectors",
    "twobga-aux",
})
STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES = frozenset(
    {
        "STAGE2_CANONICALIZATION_ERRORS",
        "STAGE2_EMPTY_CANDIDATE_POOL",
        "STAGE2_MALFORMED_RECORDS",
        "STAGE2_UNSUPPORTED_CANDIDATES_SKIPPED",
    }
)
PAGINATED_COVERAGE_GAP_INCOMPLETENESS_CODES = frozenset(
    {
        STAGE3_INELIGIBLE_RESULT_CODE,
        STAGE3_BOUND_INSUFFICIENT_RESULT_CODE,
        STAGE3_EXACTNESS_GAP_RESULT_CODE,
    }
)
PAGINATED_PERSISTENT_INCOMPLETENESS_CODES = frozenset({
    *STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES,
    *PAGINATED_COVERAGE_GAP_INCOMPLETENESS_CODES,
})
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
SECTOR_SAT_CERTIFICATE_TYPE = "qldpc-css-bb-sector-sat-exact"
SECTOR_SAT_STRICT_REPLAY_CHECKS = frozenset(
    {
        "schema",
        "certificate_sha256",
        "known_answer_sha256",
        "matrix_sha256",
        "logical_detector",
        "translation_symmetry",
        "xz_sector_isometry",
        "anchor_cover_cubes",
        "typed_lower_evidence",
        "upper_witness",
        "proof_sha256",
        "proof_metadata",
        "sector_exact_coverage_mode",
        "sector_exact_counts",
        "sector_exact_proof_binding",
        "distance_recomputed",
        "sat_rerun",
        "final_gate",
        "certificate_passed_flag",
    }
)
TWOBGA_CERTIFICATE_TYPE = "qldpc-css-bb-twobga-subsystem-exact"
TWOBGA_STRICT_REPLAY_CHECKS = frozenset(
    {
        "schema",
        "certificate_sha256",
        "known_answer_sha256",
        "matrix_sha256",
        "theorem_eligibility",
        "typed_exact_proof",
        "twobga_exact_binding",
        "independent_auxiliary_rerun",
        "final_gate",
        "stored_final_gate",
        "certificate_passed_flag",
    }
)
_PYCACHE_ENVIRONMENT_LOCK = threading.RLock()


def _twobga_expected_lower_decisions(
    certificate: Mapping[str, Any],
    *,
    replay_checks: Any,
    replay_result: Mapping[str, Any] | None = None,
) -> int | None:
    """Validate the fixed two-sector dressed-subsystem replay contract."""

    if certificate.get("certificate_type") != TWOBGA_CERTIFICATE_TYPE:
        return None
    claim = certificate.get("claim")
    exact = certificate.get("twobga_exact")
    proof = (
        claim.get("exact_distance_proof")
        if isinstance(claim, Mapping)
        else None
    )
    if not all(
        isinstance(value, Mapping)
        for value in (claim, exact, proof, replay_checks)
    ):
        return None
    assert isinstance(claim, Mapping)
    assert isinstance(exact, Mapping)
    assert isinstance(proof, Mapping)
    assert isinstance(replay_checks, Mapping)
    lower = proof.get("lower_bound_decisions")
    distance = claim.get("d")
    expected = 2
    if not (
        certificate.get("formulation")
        == "css-bb-exact-via-dressed-twobga-subsystem-v1"
        and certificate.get("independent_verification_required") is True
        and certificate.get("build_assurance")
        == "provisional-structural-replay"
        and not isinstance(distance, bool)
        and isinstance(distance, int)
        and distance > 0
        and exact.get("exact") is True
        and certificate.get("candidate_rejection") is None
        and exact.get("required_distance") == distance
        and exact.get("distance") == distance
        and exact.get("lower_bound") == distance
        and exact.get("upper_bound") == distance
        and exact.get("expected_lower_decisions") == expected
        and exact.get("completed_lower_decisions") == expected
        and proof.get("schema_version") == 1
        and proof.get("proof_type")
        == "qldpc-css-twobga-subsystem-exact-proof-v1"
        and proof.get("exact") is True
        and proof.get("required_distance") == distance
        and proof.get("lower_bound_threshold") == distance - 1
        and proof.get("distance") == distance
        and proof.get("lower_bound") == distance
        and proof.get("upper_bound") == distance
        and proof.get("required_auxiliary_sectors") == ["X", "Z"]
        and isinstance(lower, list)
        and len(lower) == expected
        and exact.get("lower_bound_decisions") == lower
        and exact.get("upper_witness") == proof.get("upper_witness")
        and exact.get("proof") == proof
        and certificate.get("theorem_eligibility")
        == proof.get("theorem_eligibility")
        and TWOBGA_STRICT_REPLAY_CHECKS.issubset(replay_checks)
        and all(replay_checks.get(name) is True for name in TWOBGA_STRICT_REPLAY_CHECKS)
    ):
        return None
    if replay_result is not None:
        rerun = replay_result.get("rerun")
        if not (
            isinstance(rerun, Mapping)
            and rerun.get("matches") is True
            and rerun.get("cardinality_encoding") == "seqcounter"
            and rerun.get("solver") == "glucose42"
            and rerun.get("completed_sectors") == expected
            and rerun.get("expected_sectors") == expected
            and replay_result.get("replay_complete") is True
        ):
            return None
    return expected


def _sector_sat_expected_lower_decisions(
    certificate: Mapping[str, Any],
    *,
    replay_checks: Any,
    replay_result: Mapping[str, Any] | None = None,
) -> int | None:
    """Validate the replay-bound sector coverage contract.

    Humanize does not independently rebuild the BB matrices here; that is the
    certificate verifier's job.  Consequently, one-sector coverage is accepted
    only when the bound verification sidecar explicitly records the successful
    fresh X/Z-isometry replay.  Merely storing ``verified=true`` in a
    certificate is never sufficient to halve the proof obligation.
    """

    if certificate.get("certificate_type") != SECTOR_SAT_CERTIFICATE_TYPE:
        return None
    claim = certificate.get("claim")
    sector_exact = certificate.get("sector_exact")
    proof = (
        claim.get("exact_distance_proof")
        if isinstance(claim, Mapping)
        else None
    )
    if not all(
        isinstance(value, Mapping)
        for value in (claim, sector_exact, proof, replay_checks)
    ):
        return None
    assert isinstance(claim, Mapping)
    assert isinstance(sector_exact, Mapping)
    assert isinstance(proof, Mapping)
    assert isinstance(replay_checks, Mapping)
    if (
        replay_checks.get("xz_sector_isometry") is not True
        or replay_checks.get("anchor_cover_cubes") is not True
    ):
        return None
    if any(
        "xz_sector_isometry" not in value
        for value in (certificate, sector_exact, proof)
    ):
        return None
    stored = proof.get("xz_sector_isometry")
    if not (
        certificate.get("xz_sector_isometry") == stored
        and sector_exact.get("xz_sector_isometry") == stored
    ):
        return None

    raw_k = claim.get("k")
    if isinstance(raw_k, bool) or not isinstance(raw_k, int) or raw_k <= 0:
        return None
    mode = proof.get("coverage_mode")
    if mode not in {"global", "first-nonzero"}:
        return None
    if sector_exact.get("coverage_mode") != mode:
        return None

    stored_cubes = proof.get("anchor_cover_cubes")
    if not (
        certificate.get("anchor_cover_cubes") == stored_cubes
        and sector_exact.get("anchor_cover_cubes") == stored_cubes
    ):
        return None
    if stored_cubes is None:
        cube_count = 1
    elif (
        isinstance(stored_cubes, list)
        and stored_cubes
        and all(isinstance(cube, Mapping) for cube in stored_cubes)
    ):
        # The verifier-side anchor_cover_cubes check is authoritative: it
        # freshly rebuilt the ordered, disjoint and exhaustive cover from the
        # reconstructed BB translation anchors.  Humanize only consumes that
        # replay-bound result and the exact solver-decision multiplicity.
        cube_count = len(stored_cubes)
    else:
        return None

    if stored is None:
        sector_count = 2
    elif isinstance(stored, Mapping):
        # These shape checks are not the authority for the reduction.  The
        # authoritative condition is the fresh-replay check above.
        if not (
            stored.get("verified") is True
            and stored.get("canonical_sector") == "X"
            and stored.get("covered_sectors") == ["X", "Z"]
            and isinstance(stored.get("report_sha256"), str)
            and re.fullmatch(r"[0-9a-f]{64}", stored["report_sha256"])
            is not None
        ):
            return None
        sector_count = 1
    else:
        return None

    expected_partitions = sector_count * (1 if mode == "global" else raw_k)
    expected = expected_partitions * cube_count
    lower = proof.get("lower_bound_decisions")
    if not (
        isinstance(lower, list)
        and len(lower) == expected
        and proof.get("expected_lower_decisions", expected) == expected
        and proof.get("completed_lower_decisions") == expected
        and sector_exact.get("expected_lower_decisions") == expected
        and sector_exact.get("completed_lower_decisions") == expected
    ):
        return None
    if stored_cubes is not None and not (
        proof.get("expected_lower_partitions") == expected_partitions
        and proof.get("completed_lower_partitions") == expected_partitions
        and sector_exact.get("expected_lower_partitions")
        == expected_partitions
        and sector_exact.get("completed_lower_partitions")
        == expected_partitions
    ):
        return None
    if stored_cubes is None:
        for value in (proof, sector_exact):
            if (
                "expected_lower_partitions" in value
                or "completed_lower_partitions" in value
            ) and not (
                value.get("expected_lower_partitions")
                == expected_partitions
                and value.get("completed_lower_partitions")
                == expected_partitions
            ):
                return None
    if replay_result is not None:
        partitions_verified = replay_result.get(
            "logical_partitions_verified",
        )
        partitions_total = replay_result.get("logical_partitions_total")
        if not (
            isinstance(partitions_verified, int)
            and not isinstance(partitions_verified, bool)
            and isinstance(partitions_total, int)
            and not isinstance(partitions_total, bool)
            and partitions_verified
            == partitions_total
            == expected_partitions
        ):
            return None
    return expected


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


def _reviewer_source_sha256() -> str:
    """Hash the reviewer implementation used by this controller process."""

    return _file_sha256(Path(__file__).with_name("reviewer.py"))


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
    hard_timeout: float | None = None,
    termination_grace: float = 5.0,
) -> subprocess.CompletedProcess[str]:
    """Run one stage in a private session with an optional outer hard wall."""

    if hard_timeout is not None:
        hard_timeout = positive_wall_timeout(
            hard_timeout,
            "stage hard timeout",
        )
    termination_grace = positive_wall_timeout(
        termination_grace,
        "stage termination grace",
    )
    with tempfile.TemporaryDirectory(prefix="qcode-stage-pycache-") as cache:
        environment = os.environ.copy()
        environment["PYTHONPYCACHEPREFIX"] = cache
        process = subprocess.Popen(
            command,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env=environment,
            start_new_session=True,
        )
        pgid = os.getpgid(process.pid)
        session_id = os.getsid(process.pid)
        leader_start_time = linux_process_start_time(process.pid)
        if (
            pgid != process.pid
            or session_id != process.pid
            or (
                sys.platform.startswith("linux")
                and leader_start_time is None
            )
        ):
            process.kill()
            process.wait()
            raise RuntimeError("stage subprocess did not establish a private session")

        def stop_private_session() -> None:
            leader_alive = process.poll() is None
            identity_changed = False
            if leader_alive:
                try:
                    if (
                        os.getpgid(process.pid) != pgid
                        or os.getsid(process.pid) != session_id
                    ):
                        identity_changed = True
                except ProcessLookupError:
                    leader_alive = False
            if identity_changed:
                try:
                    process.terminate()
                except ProcessLookupError:
                    pass
                try:
                    process.wait(timeout=termination_grace)
                except subprocess.TimeoutExpired:
                    try:
                        process.kill()
                    except ProcessLookupError:
                        pass
                    process.wait(timeout=termination_grace)
                raise RuntimeError(
                    "stage subprocess identity changed; exact leader was killed"
                )
            if not leader_alive and not process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=leader_start_time,
            ):
                return
            try:
                os.killpg(pgid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            deadline = time.monotonic() + termination_grace
            while process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=leader_start_time,
            ) and time.monotonic() < deadline:
                process.poll()
                time.sleep(min(0.01, max(0.0, deadline - time.monotonic())))
            if process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=leader_start_time,
            ):
                try:
                    os.killpg(pgid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                kill_deadline = time.monotonic() + termination_grace
                while (
                    process_group_alive(
                        pgid,
                        session_id=session_id,
                        session_leader_start_time=leader_start_time,
                    )
                    and time.monotonic() < kill_deadline
                ):
                    process.poll()
                    time.sleep(
                        min(
                            0.01,
                            max(0.0, kill_deadline - time.monotonic()),
                        )
                    )
            try:
                process.wait(timeout=termination_grace)
            except subprocess.TimeoutExpired as exc:
                raise RuntimeError(
                    "stage subprocess leader survived SIGKILL"
                ) from exc
            if process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=leader_start_time,
            ):
                raise RuntimeError(
                    "stage subprocess group survived SIGKILL"
                )

        try:
            if hard_timeout is None:
                stdout, stderr = process.communicate()
            else:
                hard_deadline = time.monotonic() + hard_timeout
                while True:
                    remaining = max(0.0, hard_deadline - time.monotonic())
                    wait_timeout = min(
                        remaining,
                        SUBPROCESS_COMMUNICATE_MAX_SLICE_S,
                    )
                    try:
                        stdout, stderr = process.communicate(
                            timeout=wait_timeout,
                        )
                        break
                    except subprocess.TimeoutExpired:
                        # An intermediate slice is only a polling boundary.
                        # Preserve the original total wall and kill the
                        # private session only when its monotonic deadline is
                        # exhausted.
                        if wait_timeout >= remaining:
                            raise
        except subprocess.TimeoutExpired as exc:
            stop_private_session()
            try:
                stdout, stderr = process.communicate(
                    timeout=termination_grace
                )
            except subprocess.TimeoutExpired as drain_exc:
                # A malicious or broken descendant may have escaped the
                # verified session while retaining an inherited pipe.  Never
                # turn output draining into a second unbounded wait.
                stdout = drain_exc.stdout or exc.stdout or exc.output
                stderr = drain_exc.stderr or exc.stderr
                for stream in (process.stdout, process.stderr):
                    if stream is not None:
                        stream.close()
            raise subprocess.TimeoutExpired(
                command,
                hard_timeout,
                output=stdout if stdout else exc.output,
                stderr=stderr if stderr else exc.stderr,
            ) from exc
        except BaseException:
            stop_private_session()
            raise
        residual_descendants = process_group_alive(
            pgid,
            session_id=session_id,
            session_leader_start_time=leader_start_time,
        )
        if residual_descendants:
            stop_private_session()
            diagnostic = (
                "stage leader exited while private-session descendants "
                "remained; descendants were terminated"
            )
            stderr = (stderr + "\n" if stderr else "") + diagnostic
            if process.returncode == 0:
                process.returncode = 70
        return subprocess.CompletedProcess(
            command,
            process.returncode,
            stdout,
            stderr,
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
    stage2_compact_low_weight_max_weight: int = 4

    stage3_top: int = 0
    stage3_timeout: float = 300
    stage3_candidate_workers: int = 1
    stage3_direction_workers: int = 4
    stage3_backend: str = "legacy-directions"
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
        if (
            not isinstance(self.stage3_backend, str)
            or self.stage3_backend not in STAGE3_BACKENDS
        ):
            raise ValueError(
                "stage3_backend must be legacy-directions, sat-sectors, "
                "or twobga-aux"
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
            isinstance(self.stage2_compact_low_weight_max_weight, bool)
            or not isinstance(self.stage2_compact_low_weight_max_weight, int)
            or self.stage2_compact_low_weight_max_weight < 1
        ):
            raise ValueError(
                "stage2_compact_low_weight_max_weight must be a positive integer"
            )
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
            "stage2_compact_low_weight_max_weight": (
                self.stage2_compact_low_weight_max_weight
            ),
            "stage3_top": self.stage3_top,
            "stage3_timeout": self.stage3_timeout,
            "stage3_candidate_workers": self.stage3_candidate_workers,
            "stage3_direction_workers": self.stage3_direction_workers,
            "stage3_backend": self.stage3_backend,
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
            if (
                flow_values.get("evolution_evaluator") == "coset-two-block"
            ):
                flow_values.setdefault("milp_top", 0)
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
            stage2_compact_low_weight_max_weight=parse_int(
                "stage2_compact_low_weight_max_weight",
                pick(
                    "stage2_compact_low_weight_max_weight",
                    "stage2",
                    "compact_low_weight_max_weight",
                    4,
                ),
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
            stage3_backend=pick(
                "stage3_backend", "stage3", "backend", "legacy-directions"
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
        # A user may deliberately start a fresh campaign with resume=False.
        # Once the durable retry controller schedules a later proof attempt,
        # however, replay-safe solver checkpoints must be retained.  This flag
        # changes only proof subprocess checkpoint reuse; pipeline stage-cache
        # reuse continues to follow config.resume.
        self._proof_retry_resume = False
        self._humanize_run_lease: _HumanizeRunLease | None = None
        self._humanize_run_lease_stack: ExitStack | None = None
        self._humanize_run_leases: dict[Path, _HumanizeRunLease] = {}
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
        previous_config = state.get("config")
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
        self._enforce_stage1_identity(previous_config=previous_config)
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

    @staticmethod
    def _serialized_stage1_identity(
        pipeline_config: Any,
    ) -> dict[str, Any] | None:
        """Recover a persisted Humanize identity without trusting history.

        Older pipeline states stored only the identity fingerprint.  Their
        previous serialized PipelineConfig is therefore the only durable
        source from which a max-round extension can be checked.  Candidate
        input identities cannot be reconstructed this way because their
        historical content hashes are intentionally absent from config.
        """

        if not isinstance(pipeline_config, Mapping):
            return None
        candidate_inputs = pipeline_config.get("candidate_inputs")
        if not isinstance(candidate_inputs, list) or candidate_inputs:
            return None
        flow_config = pipeline_config.get("flow_config")
        if isinstance(flow_config, Mapping):
            return {
                "mode": "humanize-flow",
                "flow_config": dict(flow_config),
            }
        if flow_config is not None:
            return None

        # PipelineConfig with no explicit FlowConfig uses _flow_config().
        # Rebuild that exact logical identity for legacy states.
        repo_dir = pipeline_config.get("repo_dir")
        run_id = pipeline_config.get("run_id")
        review_model = pipeline_config.get("reviewer_model")
        review_effort = pipeline_config.get("reviewer_effort")
        max_total_workers = pipeline_config.get("max_total_workers")
        if (
            not isinstance(repo_dir, str)
            or not isinstance(run_id, str)
            or not isinstance(review_model, str)
            or not isinstance(review_effort, str)
            or isinstance(max_total_workers, bool)
            or not isinstance(max_total_workers, int)
        ):
            return None
        try:
            flow = FlowConfig(
                repo_dir=Path(repo_dir),
                run_id=run_id,
                review_model=review_model,
                review_effort=review_effort,
                max_total_workers=max_total_workers,
            )
        except (TypeError, ValueError):
            return None
        return {
            "mode": "humanize-flow",
            "flow_config": flow.serializable(),
        }

    @staticmethod
    def _is_monotonic_round_extension(
        previous: Mapping[str, Any],
        current: Mapping[str, Any],
    ) -> bool:
        """Accept exactly one identity change: a strict max-round increase."""

        if (
            previous.get("mode") != "humanize-flow"
            or current.get("mode") != "humanize-flow"
        ):
            return False
        previous_flow = previous.get("flow_config")
        current_flow = current.get("flow_config")
        if not isinstance(previous_flow, Mapping) or not isinstance(
            current_flow, Mapping
        ):
            return False
        previous_context = dict(previous_flow)
        current_context = dict(current_flow)
        previous_policy_version = previous_context.get(
            "search_regime_policy_version", 1
        )
        previous_max_rounds = previous_context.pop("max_rounds", None)
        current_max_rounds = current_context.pop("max_rounds", None)
        return bool(
            isinstance(previous_max_rounds, int)
            and not isinstance(previous_max_rounds, bool)
            and isinstance(current_max_rounds, int)
            and not isinstance(current_max_rounds, bool)
            and current_max_rounds > previous_max_rounds
            # Policy V3 binds the terminal round budget into sealed regime
            # replay.  It therefore requires a fresh run_id for any budget
            # change; V1/V2 retain their historical monotonic extension lane.
            and previous_policy_version != 3
            and current_context == previous_context
        )

    def _enforce_stage1_identity(self, *, previous_config: Any) -> None:
        current_identity = self._stage1_identity()
        current = _canonical_sha256(current_identity)
        recorded = self.state.get("stage1_identity_fingerprint")
        if recorded is not None and recorded != current:
            previous_identity = self.state.get("stage1_identity")
            if (
                not isinstance(previous_identity, Mapping)
                or _canonical_sha256(previous_identity) != recorded
            ):
                previous_identity = self._serialized_stage1_identity(
                    previous_config
                )
            if (
                not isinstance(previous_identity, Mapping)
                or _canonical_sha256(previous_identity) != recorded
                or not self._is_monotonic_round_extension(
                    previous_identity,
                    current_identity,
                )
            ):
                raise ValueError(
                    "Stage 1 search identity or candidate input changed; "
                    "only a strict max_rounds increase is allowed for the "
                    "same run_id"
                )
        self.state["stage1_identity"] = current_identity
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

    @staticmethod
    def _feedback_file_descriptor(path: Path, *, label: str) -> dict[str, Any]:
        selected = _reject_symlink_components(
            path,
            classification="UNSAFE_INPUT_PATH",
            label=label,
        )
        try:
            metadata = selected.lstat()
        except OSError as exc:
            raise PipelineError(
                "INPUT_MISSING",
                f"cannot inspect {label} {selected}: {exc}",
                stage="stage1_search",
            ) from exc
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise PipelineError(
                "UNSAFE_INPUT_PATH",
                f"{label} must be a regular non-symlink file: {selected}",
                stage="stage1_search",
            )
        try:
            digest = _file_sha256(selected)
        except OSError as exc:
            raise PipelineError(
                "INPUT_MISSING",
                f"cannot hash {label} {selected}: {exc}",
                stage="stage1_search",
            ) from exc
        return {
            "path": str(selected),
            "sha256": digest,
            "bytes": int(metadata.st_size),
        }

    def _sealed_feedback_document(
        self,
        body: Mapping[str, Any],
    ) -> dict[str, Any]:
        document = dict(body)
        document["binding_sha256"] = _canonical_sha256(document)
        return document

    def _validated_sealed_feedback_document(
        self,
        value: Any,
        *,
        kind: str,
        fields: frozenset[str],
    ) -> dict[str, Any]:
        if not isinstance(value, Mapping) or set(value) != set(fields):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"{kind} fields are incomplete",
                stage="stage1_search",
            )
        document = dict(value)
        digest = document.pop("binding_sha256", None)
        if (
            not isinstance(digest, str)
            or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            or digest != _canonical_sha256(document)
            or document.get("schema_version")
            != NEGATIVE_FEEDBACK_EPOCH_SCHEMA_VERSION
            or document.get("kind") != kind
            or document.get("pipeline_run_id") != self.config.run_id
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"{kind} binding is invalid",
                stage="stage1_search",
            )
        return dict(value)

    @staticmethod
    def _feedback_epoch_run_id(
        base_run_id: str,
        *,
        feedback_epoch: int,
        archive_sha256: str,
        initial: bool,
    ) -> str:
        if initial:
            return base_run_id
        suffix = f".feedback-e{feedback_epoch}-{archive_sha256}"
        prefix_length = 128 - len(suffix)
        if prefix_length < 1:
            # ``validate_run_id`` caps the original identity at 128 bytes, but
            # leave a deterministic non-empty prefix even for a very large
            # decimal epoch.
            suffix = f".f{feedback_epoch}-{archive_sha256}"
            prefix_length = max(1, 128 - len(suffix))
        return base_run_id[:prefix_length] + suffix

    def _coset_feedback_live_archive_path(
        self,
        flow_config: FlowConfig,
    ) -> Path:
        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            resolve_archive_path,
        )

        candidate_log = (
            self.config.repo_dir
            / "results"
            / "evolution"
            / f"humanize_{flow_config.run_id}"
            / "all_codes.jsonl"
        )
        try:
            path = resolve_archive_path(candidate_log)
        except NegativeArchiveError as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"cannot resolve the coset negative archive: {exc}",
                stage="stage1_search",
            ) from exc
        if path is None:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "coset negative archive unexpectedly resolved to disabled",
                stage="stage1_search",
            )
        return _lexical_absolute(path)

    def _validate_stage1_feedback_startup(
        self,
        value: Any,
    ) -> dict[str, Any]:
        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            load_feedback_snapshot_manifest,
        )

        fields = frozenset({
            "schema_version",
            "kind",
            "pipeline_run_id",
            "flow_run_id",
            "feedback_epoch",
            "live_archive_path",
            "archive_sha256",
            "archive_binding_sha256",
            "snapshot",
            "manifest",
            "binding_sha256",
        })
        document = self._validated_sealed_feedback_document(
            value,
            kind=NEGATIVE_FEEDBACK_STARTUP_KIND,
            fields=fields,
        )
        epoch = document.get("feedback_epoch")
        live = Path(str(document.get("live_archive_path", "")))
        flow_run_id = document.get("flow_run_id")
        if (
            isinstance(epoch, bool)
            or not isinstance(epoch, int)
            or epoch < 1
            or not isinstance(flow_run_id, str)
            or not flow_run_id
            or not live.is_absolute()
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "Stage 1 negative-feedback epoch identity is invalid",
                stage="stage1_search",
            )
        try:
            from .pipeline_process import validate_run_id

            validate_run_id(flow_run_id)
        except ValueError as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"Stage 1 feedback flow identity is invalid: {exc}",
                stage="stage1_search",
            ) from exc
        descriptors: dict[str, dict[str, Any]] = {}
        for name in ("snapshot", "manifest"):
            raw = document.get(name)
            if not isinstance(raw, Mapping) or set(raw) != {
                "path", "sha256", "bytes"
            }:
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    f"Stage 1 feedback {name} descriptor is invalid",
                    stage="stage1_search",
                )
            observed = self._feedback_file_descriptor(
                Path(str(raw.get("path", ""))),
                label=f"Stage 1 feedback {name}",
            )
            if observed != dict(raw):
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    f"Stage 1 feedback {name} bytes changed",
                    stage="stage1_search",
                )
            descriptors[name] = observed
        try:
            manifest = load_feedback_snapshot_manifest(
                Path(descriptors["manifest"]["path"]),
                expected_live_archive_path=live,
                expected_snapshot_path=Path(descriptors["snapshot"]["path"]),
                expected_run_id=flow_run_id,
                expected_round_number=1,
                expected_feedback_epoch=1,
                expected_parent_snapshot_sha256=None,
            )
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"Stage 1 feedback startup cannot be replayed: {exc}",
                stage="stage1_search",
            ) from exc
        if (
            manifest.get("archive_sha256") != document.get("archive_sha256")
            or manifest.get("archive_binding_sha256")
            != document.get("archive_binding_sha256")
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "Stage 1 feedback startup archive binding changed",
                stage="stage1_search",
            )
        return document

    def _validate_stage1_feedback_consumed(
        self,
        value: Any,
    ) -> dict[str, Any]:
        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            load_feedback_snapshot_manifest,
        )

        fields = frozenset({
            "schema_version",
            "kind",
            "pipeline_run_id",
            "flow_run_id",
            "feedback_epoch",
            "round",
            "live_archive_path",
            "archive_sha256",
            "archive_binding_sha256",
            "snapshot",
            "manifest",
            "binding_sha256",
        })
        document = self._validated_sealed_feedback_document(
            value,
            kind=NEGATIVE_FEEDBACK_CONSUMED_KIND,
            fields=fields,
        )
        epoch = document.get("feedback_epoch")
        round_number = document.get("round")
        flow_run_id = document.get("flow_run_id")
        live = Path(str(document.get("live_archive_path", "")))
        if (
            isinstance(epoch, bool)
            or not isinstance(epoch, int)
            or epoch < 1
            or isinstance(round_number, bool)
            or not isinstance(round_number, int)
            or round_number < 1
            or not isinstance(flow_run_id, str)
            or not flow_run_id
            or not live.is_absolute()
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "consumed negative-feedback identity is invalid",
                stage="stage1_search",
            )
        descriptors: dict[str, dict[str, Any]] = {}
        for name in ("snapshot", "manifest"):
            raw = document.get(name)
            if not isinstance(raw, Mapping):
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    f"consumed feedback {name} descriptor is invalid",
                    stage="stage1_search",
                )
            observed = self._feedback_file_descriptor(
                Path(str(raw.get("path", ""))),
                label=f"consumed feedback {name}",
            )
            if observed != dict(raw):
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    f"consumed feedback {name} bytes changed",
                    stage="stage1_search",
                )
            descriptors[name] = observed
        try:
            manifest = load_feedback_snapshot_manifest(
                Path(descriptors["manifest"]["path"]),
                expected_live_archive_path=live,
                expected_snapshot_path=Path(descriptors["snapshot"]["path"]),
                expected_run_id=flow_run_id,
                expected_round_number=round_number,
                expected_feedback_epoch=round_number,
            )
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"consumed Stage 1 feedback cannot be replayed: {exc}",
                stage="stage1_search",
            ) from exc
        if (
            manifest.get("archive_sha256") != document.get("archive_sha256")
            or manifest.get("archive_binding_sha256")
            != document.get("archive_binding_sha256")
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "consumed Stage 1 archive binding changed",
                stage="stage1_search",
            )
        return document

    def _validate_pending_feedback_state(
        self,
        value: Any,
    ) -> dict[str, Any]:
        if not isinstance(value, Mapping) or set(value) != {
            "record", "artifact"
        }:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "pending negative-feedback state is incomplete",
                stage="stage1_search",
            )
        record_fields = frozenset({
            "schema_version",
            "kind",
            "pipeline_run_id",
            "pending_epoch",
            "live_archive_path",
            "archive_sha256",
            "archive_binding_sha256",
            "source_stage",
            "events_added",
            "binding_sha256",
        })
        record = self._validated_sealed_feedback_document(
            value.get("record"),
            kind=NEGATIVE_FEEDBACK_PENDING_KIND,
            fields=record_fields,
        )
        epoch = record.get("pending_epoch")
        events_added = record.get("events_added")
        live = Path(str(record.get("live_archive_path", "")))
        allowed_sources = {
            "stage1-cache-recovery",
            "stage1-search",
            "stage2-sector-audit",
            "stage3-direction-audit",
        }
        if (
            isinstance(epoch, bool)
            or not isinstance(epoch, int)
            or epoch < 1
            or isinstance(events_added, bool)
            or not isinstance(events_added, int)
            or events_added < 0
            or not live.is_absolute()
            or record.get("source_stage") not in allowed_sources
            or not isinstance(record.get("archive_sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", record["archive_sha256"])
            is None
            or not isinstance(record.get("archive_binding_sha256"), str)
            or re.fullmatch(
                r"[0-9a-f]{64}", record["archive_binding_sha256"]
            )
            is None
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "pending negative-feedback record is malformed",
                stage="stage1_search",
            )
        raw_artifact = value.get("artifact")
        if not isinstance(raw_artifact, Mapping) or set(raw_artifact) != {
            "path", "sha256", "bytes"
        }:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "pending negative-feedback artifact identity is malformed",
                stage="stage1_search",
            )
        artifact = self._feedback_file_descriptor(
            Path(str(raw_artifact.get("path", ""))),
            label="pending negative-feedback artifact",
        )
        if artifact != dict(raw_artifact):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "pending negative-feedback artifact bytes changed",
                stage="stage1_search",
            )
        artifact_path = Path(artifact["path"])
        try:
            artifact_path.relative_to(
                self.paths.artifacts / "negative-feedback"
            )
        except ValueError as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "pending negative-feedback artifact escaped its fixed root",
                stage="stage1_search",
            ) from exc
        if _read_json_object(artifact_path) != record:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "pending negative-feedback artifact does not match state",
                stage="stage1_search",
            )
        return {"record": record, "artifact": artifact}

    def _stage1_feedback_prepared_document(
        self,
        base_flow_config: FlowConfig,
        startup: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Seal the exact Stage 1 identity before its mutable run starts."""

        selected = self._validate_stage1_feedback_startup(startup)
        effective = replace(
            base_flow_config,
            run_id=str(selected["flow_run_id"]),
        )
        return self._sealed_feedback_document({
            "schema_version": NEGATIVE_FEEDBACK_EPOCH_SCHEMA_VERSION,
            "kind": NEGATIVE_FEEDBACK_PREPARED_KIND,
            "pipeline_run_id": self.config.run_id,
            "base_flow_run_id": base_flow_config.run_id,
            "flow_config": effective.serializable(),
            "startup": dict(selected),
        })

    def _validate_stage1_feedback_prepared(
        self,
        value: Any,
        *,
        base_flow_config: FlowConfig,
        live_archive_path: Path,
        archive_binding_sha256: str,
        expected_epoch: int,
    ) -> dict[str, Any]:
        fields = frozenset({
            "schema_version",
            "kind",
            "pipeline_run_id",
            "base_flow_run_id",
            "flow_config",
            "startup",
            "binding_sha256",
        })
        document = self._validated_sealed_feedback_document(
            value,
            kind=NEGATIVE_FEEDBACK_PREPARED_KIND,
            fields=fields,
        )
        startup = self._validate_stage1_feedback_startup(
            document.get("startup")
        )
        flow_run_id = str(startup["flow_run_id"])
        effective = replace(base_flow_config, run_id=flow_run_id)
        if (
            document.get("base_flow_run_id") != base_flow_config.run_id
            or document.get("flow_config") != effective.serializable()
            or startup.get("feedback_epoch") != expected_epoch
            or startup.get("live_archive_path") != str(live_archive_path)
            or startup.get("archive_binding_sha256")
            != archive_binding_sha256
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "prepared Stage 1 feedback identity changed",
                stage="stage1_search",
            )
        expected_run_id = self._feedback_epoch_run_id(
            base_flow_config.run_id,
            feedback_epoch=expected_epoch,
            archive_sha256=str(startup["archive_sha256"]),
            # Protocol epoch 1 is always the base identity. Legacy/preexisting
            # terminal base runs are promoted to epoch 2 before validation.
            # Never infer this flag from the untrusted flow_run_id itself.
            initial=expected_epoch == 1,
        )
        if flow_run_id != expected_run_id:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "prepared Stage 1 run id is not bound to its frozen archive",
                stage="stage1_search",
            )
        expected_round = _lexical_absolute(
            self.config.repo_dir
            / "results"
            / "humanize"
            / flow_run_id
            / "rounds"
            / "round-001"
        )
        if any(
            _lexical_absolute(Path(str(startup[name]["path"]))).parent
            != expected_round
            for name in ("snapshot", "manifest")
        ):
            raise PipelineError(
                "UNSAFE_INPUT_PATH",
                "prepared Stage 1 feedback escaped its run identity",
                stage="stage1_search",
            )
        return document

    def _write_stage1_feedback_prepared(
        self,
        base_flow_config: FlowConfig,
        startup: Mapping[str, Any],
    ) -> dict[str, Any]:
        document = self._stage1_feedback_prepared_document(
            base_flow_config,
            startup,
        )
        document = self._validate_stage1_feedback_prepared(
            document,
            base_flow_config=base_flow_config,
            live_archive_path=Path(str(startup["live_archive_path"])),
            archive_binding_sha256=str(
                startup["archive_binding_sha256"]
            ),
            expected_epoch=int(startup["feedback_epoch"]),
        )
        self.state["negative_feedback_prepared"] = document
        self._write_state()
        return document

    def _recover_terminal_stage1_feedback_prepared(
        self,
        base_flow_config: FlowConfig,
        *,
        live_archive_path: Path,
        archive_binding_sha256: str,
        expected_epoch: int,
    ) -> dict[str, Any] | None:
        """Adopt one completed flow stranded before the Stage 1 handoff.

        Cache-recovery records are immutable write-ahead evidence for a
        derived feedback identity.  A terminal Humanize state plus its sealed
        round-one snapshot is therefore sufficient to recover a flow that
        completed before the pipeline could record consumption.
        """

        feedback_root = self.paths.artifacts / "negative-feedback"
        if not feedback_root.exists():
            return None
        if feedback_root.is_symlink() or not feedback_root.is_dir():
            raise PipelineError(
                "UNSAFE_INPUT_PATH",
                "negative-feedback artifact root is unsafe",
                stage="stage1_search",
            )
        recovered: list[dict[str, Any]] = []
        pattern = (
            f"pending-epoch-{expected_epoch:04d}-"
            "*-stage1-cache-recovery.json"
        )
        for artifact_path in sorted(feedback_root.glob(pattern)):
            descriptor = self._feedback_file_descriptor(
                artifact_path,
                label="orphaned Stage 1 feedback record",
            )
            pending = self._validate_pending_feedback_state({
                "record": _read_json_object(artifact_path),
                "artifact": descriptor,
            })["record"]
            expected_artifact_path = feedback_root / (
                f"pending-epoch-{expected_epoch:04d}-"
                f"{pending['archive_sha256']}-stage1-cache-recovery.json"
            )
            if artifact_path != expected_artifact_path:
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    "orphaned Stage 1 feedback record has a non-canonical name",
                    stage="stage1_search",
                )
            if (
                pending["pending_epoch"] != expected_epoch
                or pending["live_archive_path"] != str(live_archive_path)
                or pending["archive_binding_sha256"]
                != archive_binding_sha256
                or pending["source_stage"] != "stage1-cache-recovery"
            ):
                continue
            flow_run_id = self._feedback_epoch_run_id(
                base_flow_config.run_id,
                feedback_epoch=expected_epoch,
                archive_sha256=str(pending["archive_sha256"]),
                initial=False,
            )
            effective = replace(base_flow_config, run_id=flow_run_id)
            run_root = _lexical_absolute(
                self.config.repo_dir
                / "results"
                / "humanize"
                / flow_run_id
            )
            state_path = run_root / "state.json"
            if not state_path.exists():
                continue
            state_descriptor = self._feedback_file_descriptor(
                state_path,
                label="orphaned Stage 1 state",
            )
            flow_state = _read_json_object(Path(state_descriptor["path"]))
            if flow_state.get("status") not in {
                "search-complete",
                "incomplete-unresolved",
            }:
                continue
            if (
                flow_state.get("pending_round") is not None
                or flow_state.get("config") != effective.serializable()
            ):
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    "terminal orphaned Stage 1 state is not replayable",
                    stage="stage1_search",
                )
            round_dir = run_root / "rounds" / "round-001"
            startup = self._sealed_feedback_document({
                "schema_version": NEGATIVE_FEEDBACK_EPOCH_SCHEMA_VERSION,
                "kind": NEGATIVE_FEEDBACK_STARTUP_KIND,
                "pipeline_run_id": self.config.run_id,
                "flow_run_id": flow_run_id,
                "feedback_epoch": expected_epoch,
                "live_archive_path": str(live_archive_path),
                "archive_sha256": pending["archive_sha256"],
                "archive_binding_sha256": archive_binding_sha256,
                "snapshot": self._feedback_file_descriptor(
                    round_dir / "negative-feedback-snapshot.json",
                    label="orphaned Stage 1 feedback snapshot",
                ),
                "manifest": self._feedback_file_descriptor(
                    round_dir / "negative-feedback-snapshot-manifest.json",
                    label="orphaned Stage 1 feedback manifest",
                ),
            })
            recovered.append(
                self._stage1_feedback_prepared_document(
                    base_flow_config,
                    startup,
                )
            )
        if len(recovered) > 1:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "multiple terminal Stage 1 feedback attempts require explicit recovery",
                stage="stage1_search",
            )
        return recovered[0] if recovered else None

    def _materialize_pending_feedback_record(
        self,
        *,
        live_archive_path: Path,
        archive: Mapping[str, Any],
        pending_epoch: int,
        source_stage: str,
        events_added: int,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        """Publish immutable pending evidence without changing pipeline state."""

        if (
            isinstance(pending_epoch, bool)
            or pending_epoch < 1
            or isinstance(events_added, bool)
            or events_added < 0
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "pending negative-feedback epoch is invalid",
                stage="stage1_search",
            )
        body = {
            "schema_version": NEGATIVE_FEEDBACK_EPOCH_SCHEMA_VERSION,
            "kind": NEGATIVE_FEEDBACK_PENDING_KIND,
            "pipeline_run_id": self.config.run_id,
            "pending_epoch": pending_epoch,
            "live_archive_path": str(live_archive_path),
            "archive_sha256": archive["archive_sha256"],
            "archive_binding_sha256": archive["binding"]["binding_sha256"],
            "source_stage": source_stage,
            "events_added": events_added,
        }
        document = self._sealed_feedback_document(body)
        path = (
            self.paths.artifacts
            / "negative-feedback"
            / (
                f"pending-epoch-{pending_epoch:04d}-"
                f"{archive['archive_sha256']}-{source_stage}.json"
            )
        )
        if path.exists() or path.is_symlink():
            if path.is_symlink() or not path.is_file():
                raise PipelineError(
                    "UNSAFE_OUTPUT_PATH",
                    f"pending feedback record is unsafe: {path}",
                    stage="stage1_search",
                )
            if _read_json_object(path) != document:
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    "pending feedback record changed after publication",
                    stage="stage1_search",
                )
        else:
            atomic_write_json(path, document)
        descriptor = self._feedback_file_descriptor(
            path,
            label="pending negative-feedback record",
        )
        pending_state = self._validate_pending_feedback_state({
            "record": document,
            "artifact": descriptor,
        })
        return document, pending_state

    def _write_pending_feedback_record(
        self,
        *,
        live_archive_path: Path,
        archive: Mapping[str, Any],
        pending_epoch: int,
        source_stage: str,
        events_added: int,
    ) -> dict[str, Any]:
        document, pending_state = self._materialize_pending_feedback_record(
            live_archive_path=live_archive_path,
            archive=archive,
            pending_epoch=pending_epoch,
            source_stage=source_stage,
            events_added=events_added,
        )
        self.state["negative_feedback_pending"] = pending_state
        self._write_state()
        return document

    def _prepare_stage1_feedback_epoch(
        self,
        base_flow_config: FlowConfig,
    ) -> tuple[FlowConfig, dict[str, Any]]:
        """Freeze the cross-invocation feedback input for one Stage 1 run."""

        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            load_archive,
            materialize_feedback_snapshot,
        )

        live = self._coset_feedback_live_archive_path(base_flow_config)
        try:
            current_archive = load_archive(live)
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"cannot replay the live negative archive: {exc}",
                stage="stage1_search",
            ) from exc
        record = self.state["stages"]["stage1_search"]
        previous_startup: dict[str, Any] | None = None
        previous_consumed: dict[str, Any] | None = None
        raw_startup = record.get("negative_feedback_startup")
        raw_consumed = record.get("negative_feedback_consumed")
        # A source-version change gives the default archive a new path. Avoid
        # replaying an old source-bound snapshot in that case; the Stage 1
        # source fingerprint will independently invalidate the machine cache.
        if (
            isinstance(raw_startup, Mapping)
            and raw_startup.get("live_archive_path") == str(live)
        ):
            previous_startup = self._validate_stage1_feedback_startup(
                raw_startup
            )
        if (
            isinstance(raw_consumed, Mapping)
            and raw_consumed.get("live_archive_path") == str(live)
        ):
            previous_consumed = self._validate_stage1_feedback_consumed(
                raw_consumed
            )
        if (
            previous_startup is not None
            and previous_consumed is not None
            and any(
                previous_startup[name] != previous_consumed[name]
                for name in (
                    "flow_run_id",
                    "feedback_epoch",
                    "live_archive_path",
                )
            )
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "Stage 1 startup and consumed feedback epochs disagree",
                stage="stage1_search",
            )
        if (
            previous_startup is not None
            and previous_consumed is not None
            and current_archive["archive_sha256"]
            == previous_consumed["archive_sha256"]
        ):
            raw_prepared = self.state.get("negative_feedback_prepared")
            if raw_prepared is not None:
                expected_prepared = self._stage1_feedback_prepared_document(
                    base_flow_config,
                    previous_startup,
                )
                if raw_prepared != expected_prepared:
                    raise PipelineError(
                        "STAGE1_FEEDBACK_INVALID",
                        "completed Stage 1 has a different prepared identity",
                        stage="stage1_search",
                    )
                self.state.pop("negative_feedback_prepared")
                self._write_state()
            effective = replace(
                base_flow_config,
                run_id=str(previous_startup["flow_run_id"]),
            )
            return effective, previous_startup

        completed_before = record.get("machine_status") in {
            "COMPLETED", "SKIPPED"
        }
        if previous_consumed is not None:
            feedback_epoch = int(previous_consumed["feedback_epoch"]) + 1
        elif previous_startup is not None and not completed_before:
            # Resume an interrupted first attempt against its already frozen
            # input rather than sampling newer mutable archive bytes.
            effective = replace(
                base_flow_config,
                run_id=str(previous_startup["flow_run_id"]),
            )
            return effective, previous_startup
        elif completed_before:
            # Legacy completed Stage 1 records had no feedback binding. Never
            # re-enter their search-complete Humanize identity silently.
            feedback_epoch = 2
        else:
            feedback_epoch = 1

        existing_flow_terminal = False
        base_flow_state = (
            self.config.repo_dir
            / "results"
            / "humanize"
            / base_flow_config.run_id
            / "state.json"
        )
        if (
            feedback_epoch == 1
            and previous_startup is None
            and base_flow_state.is_file()
            and not base_flow_state.is_symlink()
        ):
            state_value = _read_json_object(base_flow_state)
            existing_flow_terminal = state_value.get("status") in {
                "search-complete",
                "incomplete-unresolved",
            }
            if existing_flow_terminal:
                feedback_epoch = 2

        archive_binding_sha256 = str(
            current_archive["binding"]["binding_sha256"]
        )
        raw_prepared = self.state.get("negative_feedback_prepared")
        if raw_prepared is not None:
            prepared = self._validate_stage1_feedback_prepared(
                raw_prepared,
                base_flow_config=base_flow_config,
                live_archive_path=live,
                archive_binding_sha256=archive_binding_sha256,
                expected_epoch=feedback_epoch,
            )
            startup = dict(prepared["startup"])
            return (
                replace(
                    base_flow_config,
                    run_id=str(startup["flow_run_id"]),
                ),
                startup,
            )

        # Older controllers did not persist a dedicated prepared record.  If
        # such a controller completed Humanize but failed before adopting its
        # output, recover the one terminal identity proven by the immutable
        # cache-recovery record and round-one snapshot.  Never resample the
        # newer mutable live archive into the same feedback epoch.
        recovered = self._recover_terminal_stage1_feedback_prepared(
            base_flow_config,
            live_archive_path=live,
            archive_binding_sha256=archive_binding_sha256,
            expected_epoch=feedback_epoch,
        )
        if recovered is not None:
            self.state["negative_feedback_prepared"] = recovered
            self._write_state()
            startup = dict(recovered["startup"])
            return (
                replace(
                    base_flow_config,
                    run_id=str(startup["flow_run_id"]),
                ),
                startup,
            )

        # Transitional recovery for an interrupted pre-journal controller:
        # its machine stage_config already sealed the exact startup even
        # though the successful top-level consumption record was not written.
        attempted_config = record.get("stage_config")
        attempted_startup = (
            attempted_config.get("negative_feedback_startup")
            if isinstance(attempted_config, Mapping)
            and attempted_config.get("mode") == "humanize-flow"
            and record.get("machine_status") in {"RUNNING", "FAILED"}
            else None
        )
        if attempted_startup is not None:
            attempted = self._stage1_feedback_prepared_document(
                base_flow_config,
                attempted_startup,
            )
            attempted = self._validate_stage1_feedback_prepared(
                attempted,
                base_flow_config=base_flow_config,
                live_archive_path=live,
                archive_binding_sha256=archive_binding_sha256,
                expected_epoch=feedback_epoch,
            )
            expected_command = [
                "internal:HumanizeFlow.run",
                attempted["startup"]["flow_run_id"],
            ]
            if (
                attempted_config.get("flow_config")
                != attempted["flow_config"]
                or record.get("command") != expected_command
                or record.get("command_sha256")
                != _canonical_sha256(expected_command)
            ):
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    "interrupted Stage 1 attempt changed its sealed identity",
                    stage="stage1_search",
                )
            self.state["negative_feedback_prepared"] = attempted
            self._write_state()
            startup = dict(attempted["startup"])
            return (
                replace(
                    base_flow_config,
                    run_id=str(startup["flow_run_id"]),
                ),
                startup,
            )

        raw_pending = self.state.get("negative_feedback_pending")
        pending = (
            self._validate_pending_feedback_state(raw_pending)
            if raw_pending is not None
            else None
        )
        pending_record = pending["record"] if pending is not None else None
        if (
            isinstance(pending_record, Mapping)
            and pending_record.get("archive_sha256")
            == current_archive["archive_sha256"]
            and pending_record.get("live_archive_path") == str(live)
            and isinstance(pending_record.get("pending_epoch"), int)
            and not isinstance(pending_record.get("pending_epoch"), bool)
        ):
            if int(pending_record["pending_epoch"]) != feedback_epoch:
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    "pending feedback epoch is not the next consumed epoch",
                    stage="stage1_search",
                )
        flow_run_id = self._feedback_epoch_run_id(
            base_flow_config.run_id,
            feedback_epoch=feedback_epoch,
            archive_sha256=current_archive["archive_sha256"],
            initial=(
                feedback_epoch == 1
                and not completed_before
                and not existing_flow_terminal
            ),
        )
        effective = replace(base_flow_config, run_id=flow_run_id)
        round_dir = (
            self.config.repo_dir
            / "results"
            / "humanize"
            / flow_run_id
            / "rounds"
            / "round-001"
        )
        round_dir.mkdir(parents=True, exist_ok=True)
        snapshot_path = round_dir / "negative-feedback-snapshot.json"
        manifest_path = round_dir / "negative-feedback-snapshot-manifest.json"
        try:
            manifest = materialize_feedback_snapshot(
                live,
                snapshot_path,
                manifest_path,
                run_id=flow_run_id,
                round_number=1,
                feedback_epoch=1,
            )
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"cannot freeze the Stage 1 feedback epoch: {exc}",
                stage="stage1_search",
            ) from exc
        body = {
            "schema_version": NEGATIVE_FEEDBACK_EPOCH_SCHEMA_VERSION,
            "kind": NEGATIVE_FEEDBACK_STARTUP_KIND,
            "pipeline_run_id": self.config.run_id,
            "flow_run_id": flow_run_id,
            "feedback_epoch": feedback_epoch,
            "live_archive_path": str(live),
            "archive_sha256": manifest["archive_sha256"],
            "archive_binding_sha256": manifest["archive_binding_sha256"],
            "snapshot": self._feedback_file_descriptor(
                snapshot_path,
                label="Stage 1 feedback snapshot",
            ),
            "manifest": self._feedback_file_descriptor(
                manifest_path,
                label="Stage 1 feedback snapshot manifest",
            ),
        }
        startup = self._validate_stage1_feedback_startup(
            self._sealed_feedback_document(body)
        )
        self._write_stage1_feedback_prepared(
            base_flow_config,
            startup,
        )
        if previous_consumed is not None:
            self._write_pending_feedback_record(
                live_archive_path=live,
                archive=current_archive,
                pending_epoch=feedback_epoch,
                source_stage="stage1-cache-recovery",
                events_added=0,
            )
        return effective, startup

    def _stage1_feedback_consumption(
        self,
        startup: Mapping[str, Any],
        flow_state: Any,
    ) -> dict[str, Any]:
        """Bind the newest round snapshot actually available to Stage 1."""

        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            load_feedback_snapshot_manifest,
        )

        flow_run_id = str(startup["flow_run_id"])
        round_number = 1
        if (
            isinstance(flow_state, Mapping)
            and isinstance(flow_state.get("current_round"), int)
            and not isinstance(flow_state.get("current_round"), bool)
            and flow_state["current_round"] >= 1
        ):
            candidate_round = int(flow_state["current_round"])
            candidate_manifest = (
                self.config.repo_dir
                / "results"
                / "humanize"
                / flow_run_id
                / "rounds"
                / f"round-{candidate_round:03d}"
                / "negative-feedback-snapshot-manifest.json"
            )
            if candidate_manifest.is_file() and not candidate_manifest.is_symlink():
                round_number = candidate_round
        manifest_path = (
            self.config.repo_dir
            / "results"
            / "humanize"
            / flow_run_id
            / "rounds"
            / f"round-{round_number:03d}"
            / "negative-feedback-snapshot-manifest.json"
        )
        try:
            manifest = load_feedback_snapshot_manifest(
                manifest_path,
                expected_live_archive_path=Path(
                    str(startup["live_archive_path"])
                ),
                expected_run_id=flow_run_id,
                expected_round_number=round_number,
                expected_feedback_epoch=round_number,
            )
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"cannot bind the consumed Stage 1 feedback epoch: {exc}",
                stage="stage1_search",
            ) from exc
        snapshot_path = Path(manifest["snapshot_path"])
        body = {
            "schema_version": NEGATIVE_FEEDBACK_EPOCH_SCHEMA_VERSION,
            "kind": NEGATIVE_FEEDBACK_CONSUMED_KIND,
            "pipeline_run_id": self.config.run_id,
            "flow_run_id": flow_run_id,
            "feedback_epoch": startup["feedback_epoch"],
            "round": round_number,
            "live_archive_path": startup["live_archive_path"],
            "archive_sha256": manifest["archive_sha256"],
            "archive_binding_sha256": manifest["archive_binding_sha256"],
            "snapshot": self._feedback_file_descriptor(
                snapshot_path,
                label="consumed Stage 1 feedback snapshot",
            ),
            "manifest": self._feedback_file_descriptor(
                manifest_path,
                label="consumed Stage 1 feedback manifest",
            ),
        }
        return self._validate_stage1_feedback_consumed(
            self._sealed_feedback_document(body)
        )

    def _record_stage1_feedback_consumption(
        self,
        startup: Mapping[str, Any],
        flow_state: Any,
    ) -> dict[str, Any]:
        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            load_archive,
        )

        # Validate every dependency and materialize immutable WAL evidence
        # without mutating the caller-owned state. The caller applies this
        # delta together with machine completion to a private state copy, then
        # swaps and writes that fully-formed state exactly once.
        consumed = self._stage1_feedback_consumption(startup, flow_state)
        prepared = self._stage1_feedback_prepared_document(
            self._flow_config(),
            startup,
        )
        if self.state.get("negative_feedback_prepared") != prepared:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "Stage 1 completed under a different prepared identity",
                stage="stage1_search",
            )
        raw_pending = self.state.get("negative_feedback_pending")
        pending = (
            self._validate_pending_feedback_state(raw_pending)
            if raw_pending is not None
            else None
        )
        pending_record = pending["record"] if pending is not None else None
        consume_pending = (
            isinstance(pending_record, Mapping)
            and pending_record.get("pending_epoch")
            == consumed["feedback_epoch"]
        )
        live = Path(consumed["live_archive_path"])
        try:
            archive = load_archive(live)
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                f"cannot replay Stage 1 negative-feedback poststate: {exc}",
                stage="stage1_search",
            ) from exc

        next_pending: dict[str, Any] | None = None
        if archive["archive_sha256"] != consumed["archive_sha256"]:
            _document, next_pending = (
                self._materialize_pending_feedback_record(
                    live_archive_path=live,
                    archive=archive,
                    pending_epoch=int(consumed["feedback_epoch"]) + 1,
                    source_stage="stage1-search",
                    events_added=0,
                )
            )
        return {
            "startup": dict(startup),
            "consumed": consumed,
            "consume_pending": consume_pending,
            "next_pending": next_pending,
        }

    def _record_coset_feedback_pending(
        self,
        candidates: Sequence[Path],
        *,
        source_stage: str,
        events_added: int,
    ) -> None:
        # Existing-input campaigns have no Humanize Stage 1 to schedule on the
        # next invocation. Their verified archive remains useful to a later
        # explicitly configured search campaign, but there is no local epoch.
        if events_added <= 0 or self.config.candidate_inputs:
            return
        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            load_archive,
        )

        stages = self.state.get("stages")
        if not isinstance(stages, Mapping):
            return
        record = stages.get("stage1_search")
        if not isinstance(record, Mapping) or not isinstance(
            record.get("negative_feedback_consumed"), Mapping
        ):
            return
        consumed = self._validate_stage1_feedback_consumed(
            record.get("negative_feedback_consumed")
        )
        live = self._coset_negative_archive_path(candidates)
        try:
            archive = load_archive(live)
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                f"cannot seal the negative-feedback poststate: {exc}",
                stage=source_stage,
            ) from exc
        if archive["archive_sha256"] == consumed["archive_sha256"]:
            return
        self._write_pending_feedback_record(
            live_archive_path=live,
            archive=archive,
            pending_epoch=int(consumed["feedback_epoch"]) + 1,
            source_stage=source_stage,
            events_added=events_added,
        )

    def _reset_derived_humanize_run_leases(self) -> None:
        """Release prior proof-pass leases while retaining the base lease."""

        base_lease = self._humanize_run_lease
        lease_stack = self._humanize_run_lease_stack
        if base_lease is None or lease_stack is None:
            raise PipelineError(
                "PIPELINE_LOCK_REQUIRED",
                "proof pass cannot reset Humanize leases without the base lease",
                stage="stage1_search",
            )
        lease_stack.close()
        self._humanize_run_lease_stack = ExitStack()
        self._humanize_run_leases = {base_lease.path: base_lease}

    def _ensure_stage1_run_lease(
        self,
        flow_config: FlowConfig,
        feedback_startup: Mapping[str, Any] | None,
    ) -> _HumanizeRunLease:
        """Hold the exact Stage 1 run lease through the current proof pass."""

        base_lease = self._humanize_run_lease
        if base_lease is None:
            raise PipelineError(
                "PIPELINE_LOCK_REQUIRED",
                "Stage 1 cannot run without the campaign-wide Humanize lease",
                stage="stage1_search",
            )
        expected_root = _lexical_absolute(
            self.config.repo_dir
            / "results"
            / "humanize"
            / flow_config.run_id
        )
        target_path = expected_root / "run.lock"
        startup = (
            self._validate_stage1_feedback_startup(feedback_startup)
            if feedback_startup is not None
            else None
        )
        if (
            startup is not None
            and startup.get("flow_run_id") != flow_config.run_id
        ):
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "Stage 1 run is not bound to its sealed feedback epoch",
                stage="stage1_search",
            )
        if target_path == base_lease.path:
            return base_lease

        if startup is None:
            raise PipelineError(
                "STAGE1_FEEDBACK_INVALID",
                "derived Stage 1 run has no sealed feedback epoch",
                stage="stage1_search",
            )
        lease_stack = self._humanize_run_lease_stack
        if lease_stack is None:
            raise PipelineError(
                "PIPELINE_LOCK_REQUIRED",
                "derived Stage 1 cannot run without the campaign lease stack",
                stage="stage1_search",
            )
        effective_lease = self._humanize_run_leases.get(target_path)
        if effective_lease is not None:
            return effective_lease

        flow_store = RunStore.create(
            self.config.repo_dir / "results",
            flow_config.run_id,
        )
        if (
            _lexical_absolute(flow_store.root) != expected_root
            or flow_store.lock_path.absolute() != target_path
        ):
            raise PipelineError(
                "UNSAFE_CONTROL_PATH",
                "derived Stage 1 RunStore escaped its sealed run identity",
                stage="stage1_search",
            )
        try:
            effective_lease = lease_stack.enter_context(
                _acquire_humanize_run_lease(flow_store)
            )
        except HumanizeRunAlreadyActiveError as exc:
            raise PipelineBusyError(
                "PIPELINE_BUSY",
                "another process owns the derived Humanize run lease "
                f"for {flow_store.run_id!r}",
                stage="stage1_search",
            ) from exc
        except RoundTransactionError as exc:
            raise PipelineError(
                "UNSAFE_CONTROL_PATH",
                f"cannot acquire derived Humanize run lease: {exc}",
                stage="stage1_search",
            ) from exc
        self._humanize_run_leases[target_path] = effective_lease
        return effective_lease

    def _run_stage1_flow(
        self,
        flow: Any,
        *,
        expected_flow_config: FlowConfig | None = None,
        feedback_startup: Mapping[str, Any] | None = None,
    ) -> Any:
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
            flow_store = getattr(flow, "store", None)
            flow_config = getattr(flow, "config", None)
            if not isinstance(flow_store, RunStore) or not isinstance(
                flow_config, FlowConfig
            ):
                raise PipelineError(
                    "UNSAFE_CONTROL_PATH",
                    "lease-aware Stage 1 flow has no trusted RunStore binding",
                    stage="stage1_search",
                )
            if expected_flow_config is None:
                expected_flow_config = flow_config
            # Compare the complete immutable dataclass, not only its logical
            # checkpoint identity. ``serializable()`` deliberately omits the
            # operational worker cap so checkpoints can be resumed under a
            # newly scheduled budget; a flow factory must not use that escape
            # hatch to alter the budget sealed by this pipeline invocation.
            if flow_config != expected_flow_config:
                raise PipelineError(
                    "STAGE1_FEEDBACK_INVALID",
                    "lease-aware Stage 1 flow changed its sealed configuration",
                    stage="stage1_search",
                )
            expected_root = _lexical_absolute(
                self.config.repo_dir
                / "results"
                / "humanize"
                / expected_flow_config.run_id
            )
            target_path = flow_store.lock_path.absolute()
            if (
                flow_store.run_id != expected_flow_config.run_id
                or _lexical_absolute(flow_store.root) != expected_root
                or target_path != expected_root / "run.lock"
            ):
                raise PipelineError(
                    "UNSAFE_CONTROL_PATH",
                    "lease-aware Stage 1 flow store does not match its run identity",
                    stage="stage1_search",
                )
            run_lease = self._ensure_stage1_run_lease(
                expected_flow_config,
                feedback_startup,
            )
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
                    if (
                        self._humanize_run_lease is not None
                        or self._humanize_run_lease_stack is not None
                        or self._humanize_run_leases
                    ):
                        raise PipelineError(
                            "PIPELINE_BUSY",
                            "pipeline already owns a Humanize run lease",
                        )
                    derived_lease_stack = ExitStack()
                    try:
                        self._humanize_run_lease = run_lease
                        self._humanize_run_lease_stack = derived_lease_stack
                        self._humanize_run_leases = {
                            run_lease.path: run_lease,
                        }
                        yield
                    finally:
                        try:
                            active_derived_stack = (
                                self._humanize_run_lease_stack
                            )
                            if active_derived_stack is not None:
                                active_derived_stack.close()
                        finally:
                            self._humanize_run_leases = {}
                            self._humanize_run_lease_stack = None
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
        action_catalog = (
            self.config.repo_dir
            / "evaluation"
            / "coset_two_block_actions.v1.json"
        )
        action_catalog_v2 = (
            self.config.repo_dir
            / "evaluation"
            / "coset_two_block_actions.v2.json"
        )
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
                self.config.repo_dir / "scripts" / "screen_frontier_sat.py",
                self.config.repo_dir / "scripts" / "screen_frontier_xor.py",
                registry,
            ),
            "known_code_registry_sha256": self._source_file_sha256(
                registry,
                label="known-code registry",
            ),
            **({
                "coset_action_catalog_sha256": self._source_file_sha256(
                    action_catalog,
                    label="coset two-block action catalog",
                ),
            } if action_catalog.exists() else {}),
            **({
                "coset_action_catalog_v2_sha256": self._source_file_sha256(
                    action_catalog_v2,
                    label="coset two-block action catalog v2",
                ),
            } if action_catalog_v2.exists() else {}),
            **self._worker_runtime_provenance(),
        }

    def _strict_source_provenance(self) -> dict[str, Any]:
        registry = self.config.repo_dir / "results" / "known_code_registry.json"
        action_catalog = (
            self.config.repo_dir
            / "evaluation"
            / "coset_two_block_actions.v1.json"
        )
        action_catalog_v2 = (
            self.config.repo_dir
            / "evaluation"
            / "coset_two_block_actions.v2.json"
        )
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
                *self._strict_verifier_sources(),
                runner,
                registry,
            ),
            "known_code_registry_sha256": self._source_file_sha256(
                registry,
                label="known-code registry",
            ),
            **({
                "coset_action_catalog_sha256": self._source_file_sha256(
                    action_catalog,
                    label="coset two-block action catalog",
                ),
            } if action_catalog.exists() else {}),
            **({
                "coset_action_catalog_v2_sha256": self._source_file_sha256(
                    action_catalog_v2,
                    label="coset two-block action catalog v2",
                ),
            } if action_catalog_v2.exists() else {}),
            "strict_runner_sha256": self._source_file_sha256(
                runner,
                label="strict known-answer runner",
            ),
            **self._worker_runtime_provenance(),
        }

    def _strict_verifier_sources(self) -> tuple[Path, ...]:
        """Return script modules imported by Stage 5 certificate replay."""

        scripts = self.config.repo_dir / "scripts"
        return (
            scripts / "screen_frontier_candidate.py",
            scripts / "screen_frontier_sat.py",
            scripts / "screen_frontier_xor.py",
            scripts / "screen_frontier_twobga.py",
        )

    def _stage1_source_provenance(self) -> dict[str, Any]:
        action_catalog = (
            self.config.repo_dir
            / "evaluation"
            / "coset_two_block_actions.v1.json"
        )
        action_catalog_v2 = (
            self.config.repo_dir
            / "evaluation"
            / "coset_two_block_actions.v2.json"
        )
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
            **({
                "coset_action_catalog_sha256": self._source_file_sha256(
                    action_catalog,
                    label="coset two-block action catalog",
                ),
            } if action_catalog.exists() else {}),
            **({
                "coset_action_catalog_v2_sha256": self._source_file_sha256(
                    action_catalog_v2,
                    label="coset two-block action catalog v2",
                ),
            } if action_catalog_v2.exists() else {}),
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

    @staticmethod
    def _reset_new_attempt_evidence(record: dict[str, Any]) -> None:
        """Remove terminal evidence that belongs to an earlier attempt."""

        record["review_status"] = "PENDING"
        for field_name in (
            "accepted_nonzero_output",
            "advisory_failure",
            "bitlesson_ids",
            "candidate_inputs",
            "failure",
            "finished_at",
            "incomplete_at",
            "incomplete_reasons",
            "invalidated_at",
            "invalidation_reason",
            "machine_completed_at",
            "machine_summary",
            "output_hashes",
            "resumed_machine",
            "review_error",
            "review_fingerprint",
            "review_finished_at",
            "review_machine_output_hashes",
            "review_path",
            "review_started_at",
        ):
            record.pop(field_name, None)

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
            if self.command_runner is default_command_runner:
                completed = default_command_runner(
                    command,
                    cwd=self.config.repo_dir,
                    hard_timeout=self._stage_outer_hard_timeout(stage),
                )
            else:
                completed = self.command_runner(
                    command,
                    cwd=self.config.repo_dir,
                )
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

    def _stage_outer_hard_timeout(self, stage: str) -> float | None:
        """Return a final process wall beyond each proof stage's inner walls."""

        if stage == "stage3_direction_audit":
            try:
                rows = [
                    json.loads(line)
                    for line in self.paths.stage2_ranked.read_text().splitlines()
                    if line.strip()
                ]
            except (OSError, UnicodeError, json.JSONDecodeError) as exc:
                raise PipelineError(
                    "STAGE_TIMEOUT_BUDGET",
                    f"cannot derive Stage 3 outer wall: {exc}",
                    stage=stage,
                ) from exc
            if not all(isinstance(row, Mapping) for row in rows):
                raise PipelineError(
                    "STAGE_TIMEOUT_BUDGET",
                    "cannot derive Stage 3 outer wall from non-object rows",
                    stage=stage,
                )
            # Use the exact same candidate-dependent planner as the isolated
            # Stage 3 worker.  In particular, SAT work is
            # sectors * (k * anchor-cubes + optional global-lower + upper),
            # not a fixed 2*k expression.
            from scripts.audit_direction_pool import expected_proof_units

            seen: set[str] = set()
            candidate_units: list[int] = []
            for index, row in enumerate(rows):
                audit = row.get("campaign_audit")
                if not isinstance(audit, Mapping) or (
                    audit.get("status") != "UNRESOLVED"
                ):
                    continue
                identity = row.get("triage_identity")
                digest = (
                    identity.get("canonical_digest")
                    if isinstance(identity, Mapping)
                    else row.get("canonical_digest")
                )
                key = str(digest) if isinstance(digest, str) else f"row-{index}"
                if key in seen:
                    continue
                seen.add(key)
                try:
                    units = expected_proof_units(
                        row, self.config.stage3_backend,
                    )
                except (KeyError, TypeError, ValueError):
                    # Invalid candidates fail before solver launch.  Keep a
                    # finite controller allowance for setup/error reporting.
                    units = 1
                candidate_units.append(units)
            direction_workers = self.config.stage3_direction_workers
            direction_wall = (
                self._scaled_proof_timeout(self.config.stage3_timeout) + 5.0
            )
            screening_wall = sum(
                (
                    (
                        proof_units
                        + direction_workers
                        - 1
                    )
                    // direction_workers
                )
                * direction_wall
                + 6.0
                for proof_units in candidate_units
            )
            certificate_wall = (
                self._scaled_proof_timeout(
                    self.config.certificate_total_timeout
                )
                + self._scaled_proof_timeout(
                    self.config.verification_total_timeout
                )
                + 6.0
            )
            certificate_waves = math.ceil(
                len(candidate_units) / self.config.certificate_workers
            )
            outer = screening_wall + certificate_waves * certificate_wall + 60.0
            if not math.isfinite(outer) or outer <= 0:
                raise PipelineError(
                    "STAGE_TIMEOUT_BUDGET",
                    "derived Stage 3 outer wall is not positive and finite",
                    stage=stage,
                )
            return outer
        if stage != "stage5_strict_gate":
            return None
        multiplier = float(self._proof_budget_multiplier)
        known_answer_total = math.ceil(
            float(self.config.known_answer_total_timeout) * multiplier
        )
        known_answer_margin = max(
            60,
            (known_answer_total + 19) // 20,
        )
        known_answer_outer = (
            3 * known_answer_total + known_answer_margin + 5
        )
        verification_total = (
            float(self.config.verification_total_timeout) * multiplier
        )
        # Internal workers own the mathematical timeout and checkpoint result.
        # This small outer cushion only covers serialization and interpreter
        # cleanup if the finalizer itself becomes wedged.
        return known_answer_outer + verification_total + 30.0

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
                "review_schema_sha256": _canonical_sha256(REVIEW_SCHEMA),
                "reviewer_source_sha256": _reviewer_source_sha256(),
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
            # Every pipeline-level review is advisory. The mandatory Humanize
            # search-review loop runs inside HumanizeFlow and is unaffected by
            # an outer checkpoint-review outage.
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
            self._reset_new_attempt_evidence(record)
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
        feedback_startup: dict[str, Any] | None = None
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
            base_flow_config = self._flow_config()
            if base_flow_config.evolution_evaluator == "coset-two-block":
                flow_config, feedback_startup = (
                    self._prepare_stage1_feedback_epoch(base_flow_config)
                )
            else:
                flow_config = base_flow_config
            # Acquire a derived feedback run lease before cache validation.
            # A cache hit skips HumanizeFlow.run(), but its candidate/state
            # files must remain protected through the downstream proof stages.
            if (
                feedback_startup is not None
                and flow_config.run_id != base_flow_config.run_id
            ):
                self._ensure_stage1_run_lease(
                    flow_config,
                    feedback_startup,
                )
            flow_holder: dict[str, Any] = {}
            command = ["internal:HumanizeFlow.run", flow_config.run_id]

            def current_stage_config() -> dict[str, Any]:
                value = {
                    "mode": "humanize-flow",
                    "flow_config": flow_config.serializable(),
                    **self._stage1_source_provenance(),
                }
                if feedback_startup is not None:
                    value["negative_feedback_startup"] = dict(
                        feedback_startup
                    )
                return value

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
                        feedback_environment = {
                            "QCODE_COSET_NEGATIVE_ARCHIVE_PATH": (
                                os.environ.get(
                                    "QCODE_COSET_NEGATIVE_ARCHIVE_PATH"
                                )
                            ),
                            "QCODE_COSET_NEGATIVE_ARCHIVE_SNAPSHOT_PATH": (
                                os.environ.get(
                                    "QCODE_COSET_NEGATIVE_ARCHIVE_SNAPSHOT_PATH"
                                )
                            ),
                        }
                        if feedback_startup is not None:
                            os.environ[
                                "QCODE_COSET_NEGATIVE_ARCHIVE_PATH"
                            ] = str(feedback_startup["live_archive_path"])
                            # Each managed Humanize round installs its own
                            # frozen snapshot. Never let a caller's stale read
                            # view bleed into that transaction.
                            os.environ.pop(
                                "QCODE_COSET_NEGATIVE_ARCHIVE_SNAPSHOT_PATH",
                                None,
                            )
                        try:
                            flow = self.flow_factory(flow_config)
                            flow_holder["flow"] = flow
                            try:
                                flow_state = self._run_stage1_flow(
                                    flow,
                                    expected_flow_config=flow_config,
                                    feedback_startup=feedback_startup,
                                )
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
                            if (
                                not isinstance(flow_state, Mapping)
                                or flow_state.get("status")
                                not in {
                                    "search-complete",
                                    "incomplete-unresolved",
                                }
                            ):
                                raise PipelineError(
                                    "STAGE1_INCOMPLETE",
                                    "HumanizeFlow produced no auditable "
                                    "Stage 1 handoff",
                                    stage=stage,
                                )
                            flow_holder["state"] = flow_state
                            # HumanizeFlow discovers outputs by replaying every
                            # committed round binding. A feedback-derived run
                            # must do that while the sealed base live-archive
                            # identity is still installed; otherwise the
                            # candidate-log fallback derives a different path
                            # and rejects its valid immutable manifests.
                            flow_holder["candidates"] = (
                                self._discover_flow_outputs(flow, flow_state)
                            )
                        finally:
                            sys.pycache_prefix = previous_cache_prefix
                            if cache_environment_present:
                                assert previous_cache_environment is not None
                                os.environ["PYTHONPYCACHEPREFIX"] = (
                                    previous_cache_environment
                                )
                            else:
                                os.environ.pop("PYTHONPYCACHEPREFIX", None)
                            for name, original in feedback_environment.items():
                                if original is None:
                                    os.environ.pop(name, None)
                                else:
                                    os.environ[name] = original
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
        if not self.config.candidate_inputs and feedback_startup is not None:
            input_paths.extend([
                Path(feedback_startup["snapshot"]["path"]),
                Path(feedback_startup["manifest"]["path"]),
            ])
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
        self._reset_new_attempt_evidence(record)
        self.state["active_stage"] = stage
        self._write_state()
        feedback_transition: dict[str, Any] | None = None
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
                candidates = list(flow_holder.get("candidates", ()))
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
            if not self.config.candidate_inputs and feedback_startup is not None:
                feedback_transition = self._record_stage1_feedback_consumption(
                    feedback_startup,
                    flow_holder.get("state"),
                )
        except PipelineError:
            raise
        except Exception as exc:
            raise PipelineError(
                "STAGE1_FAILED",
                f"{type(exc).__name__}: {exc}",
                stage=stage,
            ) from exc

        # Build the complete adoption on a private copy.  Until the single
        # pointer swap below, signal/error handling can only persist the prior
        # prepared state; after the swap it can only persist a fully completed
        # machine record.  Immutable pending evidence may already exist, but
        # it is merely an unreferenced WAL artifact until this commit.
        completed_state = copy.deepcopy(self.state)
        completed_record = completed_state["stages"][stage]
        if feedback_transition is not None:
            completed_record["negative_feedback_startup"] = dict(
                feedback_transition["startup"]
            )
            completed_record["negative_feedback_consumed"] = dict(
                feedback_transition["consumed"]
            )
            completed_state["negative_feedback_active"] = dict(
                feedback_transition["consumed"]
            )
            completed_state.pop("negative_feedback_prepared", None)
            if feedback_transition["consume_pending"]:
                completed_state.pop("negative_feedback_pending", None)
            if feedback_transition["next_pending"] is not None:
                completed_state["negative_feedback_pending"] = dict(
                    feedback_transition["next_pending"]
                )
        completed_record["exit_code"] = 0
        completed_record["machine_status"] = "COMPLETED"
        completed_record["status"] = "COMPLETED"
        completed_record["machine_completed_at"] = utc_now()
        completed_record["output_hashes"] = output_hashes
        completed_record["candidate_inputs"] = [
            str(path) for path in candidates
        ]
        completed_record["review_status"] = (
            "MANAGED_BY_HUMANIZE" if not self.config.candidate_inputs else "PENDING"
        )
        completed_record["finished_at"] = utc_now()
        completed_record["resumed_machine"] = False
        self.state = completed_state
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
        missing = object()
        if isinstance(returned, Mapping):
            values = returned.get(
                "pipeline_candidate_inputs", returned.get("candidate_inputs")
            )
        if (
            values is None
            and inspect.getattr_static(
                flow,
                "pipeline_candidate_inputs",
                missing,
            )
            is not missing
        ):
            # Avoid ``hasattr`` here: descriptors are executable, so a
            # property-backed history replay would otherwise run twice and an
            # AttributeError raised inside it would be mistaken for absence.
            values = getattr(flow, "pipeline_candidate_inputs")
        if (
            values is None
            and inspect.getattr_static(flow, "candidate_log", missing)
            is not missing
        ):
            values = [getattr(flow, "candidate_log")]
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

    def _coset_negative_archive_path(
        self,
        candidates: Sequence[Path],
    ) -> Path:
        """Resolve the one source-versioned archive shared by search rounds."""

        from evolve.coset_negative_archive import resolve_archive_path

        if self.config.candidate_inputs:
            if not candidates:
                raise PipelineError(
                    "OUTPUT_MISSING",
                    "cannot place the coset negative archive without candidates",
                    stage="stage1_search",
                )
            candidate_log = candidates[0]
        else:
            # A feedback epoch may run under a derived Humanize/evolution
            # identity. Stage 2/3 must append to the exact live archive frozen
            # into that Stage 1 handoff, regardless of the derived candidate
            # log path or a subsequently changed process environment.
            stage1 = self.state.get("stages", {}).get("stage1_search", {})
            raw_consumed = (
                stage1.get("negative_feedback_consumed")
                if isinstance(stage1, Mapping)
                else None
            )
            raw_startup = (
                stage1.get("negative_feedback_startup")
                if isinstance(stage1, Mapping)
                else None
            )
            if isinstance(raw_consumed, Mapping):
                consumed = self._validate_stage1_feedback_consumed(
                    raw_consumed
                )
                return Path(str(consumed["live_archive_path"]))
            if isinstance(raw_startup, Mapping):
                startup = self._validate_stage1_feedback_startup(raw_startup)
                return Path(str(startup["live_archive_path"]))
            candidate_log = (
                self.config.repo_dir
                / "results"
                / "evolution"
                / f"humanize_{self.config.run_id}"
                / "all_codes.jsonl"
            )
        path = resolve_archive_path(candidate_log)
        if path is None:
            raise PipelineError(
                "OUTPUT_INVALID",
                "coset negative archive unexpectedly resolved to disabled",
                stage="stage1_search",
            )
        return path

    def _archive_stage2_coset_negatives(
        self,
        candidates: Sequence[Path],
    ) -> dict[str, Any]:
        """Replay Stage-2 sparse-kernel witnesses into next-round memory."""

        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            ingest_stage2_paths,
        )

        try:
            summary = ingest_stage2_paths(
                self._coset_negative_archive_path(candidates),
                [self.paths.stage2_summary],
            )
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                f"Stage 2 negative archive replay failed: {exc}",
                stage="stage2_sector_audit",
            ) from exc
        self.state["negative_mechanism_archive"] = summary
        self._write_state()
        self._record_coset_feedback_pending(
            candidates,
            source_stage="stage2-sector-audit",
            events_added=int(summary.get("events_added", 0)),
        )
        return summary

    def _archive_stage3_coset_negatives(
        self,
        candidates: Sequence[Path],
        stage3: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Replay terminal SAT rejections before any later search extension."""

        from evolve.coset_negative_archive import (
            NegativeArchiveError,
            ingest_stage3_paths,
            load_archive,
        )

        paths: list[Path] = []
        for result in stage3.get("results", []):
            if not isinstance(result, Mapping):
                continue
            if (
                result.get("backend") != "sat-sectors"
                or result.get("status") != "REJECTED"
            ):
                continue
            raw_path = result.get("artifact_path")
            if not isinstance(raw_path, str) or not raw_path:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 3 SAT rejection has no artifact path",
                    stage="stage3_direction_audit",
                )
            path = Path(raw_path)
            if not path.is_absolute():
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 3 SAT rejection artifact path is not absolute",
                    stage="stage3_direction_audit",
                )
            paths.append(path)
        archive_path = self._coset_negative_archive_path(candidates)
        try:
            if paths:
                summary = ingest_stage3_paths(archive_path, paths)
            else:
                archive = load_archive(archive_path)
                source_counts: dict[str, int] = {}
                for event in archive["events"].values():
                    source = str(event["proof"]["source"])
                    source_counts[source] = source_counts.get(source, 0) + 1
                summary = {
                    "enabled": True,
                    "binding_sha256": archive["binding"]["binding_sha256"],
                    "event_count": len(archive["events"]),
                    "motif_count": len(archive["motifs"]),
                    "coordinate_count": len(archive["coordinate_aggregates"]),
                    "events_added": 0,
                    "source_counts": dict(sorted(source_counts.items())),
                }
        except (OSError, NegativeArchiveError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                f"Stage 3 negative archive replay failed: {exc}",
                stage="stage3_direction_audit",
            ) from exc
        self.state["negative_mechanism_archive"] = summary
        self._write_state()
        self._record_coset_feedback_pending(
            candidates,
            source_stage="stage3-direction-audit",
            events_added=int(summary.get("events_added", 0)),
        )
        return summary

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
        resume_proof_state = self.config.resume or self._proof_retry_resume
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
            "--compact-low-weight-max-weight",
            str(self.config.stage2_compact_low_weight_max_weight),
            "--certificate-workers",
            str(self.config.certificate_workers),
            "--certificate-solver-workers",
            str(self.config.certificate_solver_workers),
            "--max-total-workers",
            str(self.config.max_total_workers),
            "--structural-cache-dir",
            str(
                self.paths.solver_state
                / "stage2-structural-screen-cache-v1"
            ),
            "--structural-hard-timeout",
            str(self._scaled_proof_timeout(self.config.stage2_timeout)),
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
            "--resume" if resume_proof_state else "--no-resume",
        ]
        return command

    def _stage2_selection_ledger_prestate_sha256(self) -> str | None:
        """Bind Stage 2 caching to the ledger state seen before its machine.

        The proof CLI is the transaction owner and may legitimately replace
        this ledger while it runs.  Callers must therefore capture this value
        once for the cache key and must not dynamically re-read it during the
        post-machine source/config replay.
        """

        self._ensure_solver_state_tree_safe()
        hashes = _hash_paths(
            [self.paths.stage2_selection_ledger],
            require=False,
            classification="UNSAFE_CONTROL_PATH",
            label="Stage 2 selection ledger prestate",
        )
        return hashes[
            str(_lexical_absolute(self.paths.stage2_selection_ledger))
        ]

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
            "backend": self.config.stage3_backend,
            "proof_unit_semantics": (
                "first-nonzero-sector-partitions-plus-xz-upper-witness"
                if self.config.stage3_backend == "sat-sectors"
                else (
                    "rank-defect-gated-dressed-subsystem-xz-plus-original-upper"
                    if self.config.stage3_backend == "twobga-aux"
                    else "logical-basis-directions"
                )
            ),
            "threshold_only": (
                self.config.stage3_backend != "sat-sectors"
                and not self.config.stage3_exact
            ),
            "status_counts": {},
            "retry_required": False,
            "retry_reasons": {
                "unresolved_candidates": 0,
                "unselected_unresolved_candidates": 0,
                "operational_errors": 0,
            },
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
        resume_proof_state = self.config.resume or self._proof_retry_resume
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
            "--backend",
            self.config.stage3_backend,
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
            "--resume" if resume_proof_state else "--no-resume",
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
        allow_retry_required: bool = False,
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
            "INELIGIBLE",
            "BOUND_INSUFFICIENT",
            "EXACTNESS_GAP",
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
            result_retry = result.get("retry_required", False)
            if not isinstance(result_retry, bool):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.results[{index}].retry_required must be boolean",
                )
            compact_ladder = result.get("compact_low_weight_sat_ladder")
            sparse_oracle = result.get("two_block_sparse_kernel_oracle")
            if sparse_oracle is not None:
                if not isinstance(sparse_oracle, Mapping):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{path}.results[{index}] sparse oracle is malformed",
                )
                sparse_outcome = sparse_oracle.get("outcome")
                if sparse_outcome not in {
                    "SAT",
                    "NO_SINGLE_BLOCK_WITNESS",
                    "UNKNOWN",
                }:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{path}.results[{index}] sparse oracle was not run",
                    )
                if sparse_outcome == "SAT":
                    if status != "REJECTED" or result_retry:
                        raise PipelineError(
                            "OUTPUT_INVALID",
                            f"{path}.results[{index}] sparse SAT did not reject",
                        )
                elif (
                    status != "ERROR"
                    and compact_ladder is None
                ):
                    # NO_SINGLE_BLOCK_WITNESS is not a global lower bound and
                    # sparse UNKNOWN is only advisory. Neither may substitute
                    # for the mandatory unrestricted SAT rung.
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{path}.results[{index}] compact candidate did not run "
                        "the unrestricted low-weight gate",
                    )
            if compact_ladder is not None:
                if not isinstance(compact_ladder, Mapping):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{path}.results[{index}] compact ladder is malformed",
                    )
                compact_outcome = compact_ladder.get("outcome")
                valid_compact_semantics = bool(
                    (
                        compact_outcome == "SAT"
                        and status == "REJECTED"
                        and not result_retry
                    )
                    or (
                        compact_outcome == "UNSAT"
                        and status == "UNRESOLVED"
                        and not result_retry
                        and isinstance(result.get("distance_lower_bound"), int)
                    )
                    or (
                        compact_outcome == "UNKNOWN"
                        and status == "UNRESOLVED"
                        and result_retry
                    )
                )
                if not valid_compact_semantics:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{path}.results[{index}] compact ladder semantics conflict",
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
        selected_ranked_rows: dict[str, dict[str, Any]] = {}
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
                selected_digest = selection_row_digests[0]
                if selected_digest in selected_ranked_rows:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{ranked} repeats selected candidate {selected_digest!r}",
                    )
                selected_digests.add(selected_digest)
                selected_ranked_rows[selected_digest] = row
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
        if expected_gate == "qldpc-proof-oriented-candidate-pool":
            # A compact/coset construction may enter generic Stage 3 only
            # after the mandatory unrestricted oracle produced a complete
            # UNSAT result.  The restricted two-block oracle is advisory and
            # a bare ``UNRESOLVED, retry_required=false`` is not proof of this
            # prerequisite.  Bind the requirement to the authoritative
            # selected ranked row so deleting both ladder fields cannot turn
            # a compact candidate into an eligible Stage-3 input.
            for digest, result in results_by_digest.items():
                ranked_row = selected_ranked_rows[digest]
                compact = isinstance(ranked_row.get("construction"), Mapping)
                advances = bool(
                    result.get("status") == "UNRESOLVED"
                    and result.get("retry_required", False) is False
                )
                if not (compact and advances):
                    continue
                ladder = result.get("compact_low_weight_sat_ladder")
                max_weight = (
                    ladder.get("max_weight")
                    if isinstance(ladder, Mapping) else None
                )
                lower_bound = (
                    ladder.get("distance_lower_bound")
                    if isinstance(ladder, Mapping) else None
                )
                if not (
                    isinstance(ladder, Mapping)
                    and ladder.get("schema_version") == 1
                    and ladder.get("gate")
                    == "qldpc-stage2-compact-low-weight-gate"
                    and ladder.get("outcome") == "UNSAT"
                    and ladder.get("decision_complete") is True
                    and ladder.get("retryable") is False
                    and isinstance(max_weight, int)
                    and not isinstance(max_weight, bool)
                    and max_weight >= 1
                    and lower_bound == max_weight + 1
                    and result.get("distance_lower_bound") == lower_bound
                    and result.get("deferred_backend") == "generic-global-sat"
                ):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        f"{path}.results for compact candidate {digest!r} "
                        "lacks a complete unrestricted UNSAT prerequisite",
                    )
        selection_exhausted = summary.get("selection_exhausted")
        if not isinstance(selection_exhausted, bool):
            raise PipelineError(
                "OUTPUT_INVALID",
                f"{path}.selection_exhausted must be boolean",
            )
        if expected_gate in {
            "qldpc-proof-oriented-candidate-pool",
            "qldpc-direction-candidate-pool",
        }:
            # Both proof CLIs explicitly bind process exit status to retryable
            # work. Stage 2 uses per-result markers so an ordinary UNSAT
            # compact prefilter may proceed to Stage 3 while UNKNOWN cannot.
            retry_required = summary.get("retry_required")
            if not isinstance(retry_required, bool):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.retry_required must be boolean",
                )
            if expected_gate == "qldpc-direction-candidate-pool":
                expected_retry_required = bool(
                    not selection_exhausted
                    or computed_counts.get("UNRESOLVED", 0)
                    or has_operational_errors
                )
            else:
                expected_retry_required = bool(
                    has_operational_errors
                    or any(
                        result.get("retry_required") is True
                        for result in results_by_digest.values()
                    )
                )
            if retry_required is not expected_retry_required:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.retry_required contradicts the bound results",
                )
            if retry_required and not allow_retry_required:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path} requires retry but the proof CLI exited 0",
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
            snapshot_identity = selection_page.get(
                "snapshot_identity_sha256"
            )
            page_sequence = selection_page.get("page_sequence")
            previous_ack_sha256 = selection_page.get(
                "previous_ack_sha256"
            )
            start_index = selection_page.get("start_index")
            next_index = selection_page.get("next_index")
            page_digests = selection_page.get("selected_digests")
            scan_evidence = selection_page.get("scan_evidence")
            page_sha256 = selection_page.get("page_sha256")
            if (
                not isinstance(binding, str)
                or not re.fullmatch(r"[0-9a-f]{64}", binding)
                or not is_selection_sha256(snapshot_identity)
                or isinstance(page_sequence, bool)
                or not isinstance(page_sequence, int)
                or page_sequence < 0
                or not is_selection_sha256(previous_ack_sha256)
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
                or not isinstance(scan_evidence, Mapping)
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.selection_page is malformed",
                )
            try:
                validate_scan_evidence(
                    scan_evidence,
                    snapshot_identity_sha256_value=snapshot_identity,
                    snapshot_rows=scan_evidence.get("snapshot_rows"),
                    eligible_rows=scan_evidence.get("eligible_rows"),
                    start_index=start_index,
                    next_index=next_index,
                    selection_exhausted=selection_exhausted,
                )
            except (TypeError, ValueError) as exc:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.selection_page scan evidence is invalid",
                ) from exc
            zero_pool_root = bool(
                page_sequence == 0
                and start_index == 0
                and next_index == 0
                and scan_evidence.get("eligible_rows") == 0
                and selection_exhausted
            )
            if not page_digests and not (
                next_index > start_index
                or zero_pool_root
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    f"{path}.selection_page has no trusted scan progress",
                )
            unsigned_page = dict(selection_page)
            unsigned_page.pop("page_sha256", None)
            expected_page_sha256 = _audit_json_sha256(unsigned_page)
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
        """Validate a proof CLI's recoverable exit artifact fail closed.

        Solver/certificate errors and explicit Stage-3 retry requirements are
        retained as incomplete proof work.  The only route from such an
        artifact to WIN is the independent Stage 4 certificate replay below;
        a poison-only artifact therefore remains fail closed.
        """

        summary = cls._validate_pool_summary(
            path,
            ranked,
            expected_gate,
            allow_operational_errors=True,
            allow_retry_required=True,
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
        reported_retry = bool(
            summary.get("retry_required") is True
        )
        if not (reported_error or reported_retry):
            raise PipelineError(
                "STAGE_EXIT_NONZERO",
                f"{path} exited 2 without a bound recoverable-proof record",
                stage=(
                    "stage2_sector_audit"
                    if expected_gate == "qldpc-proof-oriented-candidate-pool"
                    else "stage3_direction_audit"
                ),
                exit_code=2,
            )
        return summary

    def _validate_stage2_selection_lifecycle(
        self,
        summary: dict[str, Any],
    ) -> dict[str, Any]:
        """Bind every Stage 2 result to the sealed pending ledger page."""

        page = summary.get("selection_page")
        if page is None:
            # Legacy unpaginated artifacts remain readable, but never provide
            # cursor evidence for automatic acknowledgement.
            return summary
        if (
            not isinstance(page, Mapping)
            or not self.paths.stage2_selection_ledger.is_file()
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 selection page lacks its durable ledger",
                stage="stage2_sector_audit",
            )
        ledger = self._validated_stage2_selection_ledger(
            _read_json_object(self.paths.stage2_selection_ledger)
        )
        if ledger.get("pending") != dict(page):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 summary is not the ledger's pending page",
                stage="stage2_sector_audit",
            )
        try:
            validate_selection_page(
                page,
                binding_sha256=ledger["binding_sha256"],
                snapshot_identity_sha256_value=ledger[
                    "snapshot_identity_sha256"
                ],
                snapshot_rows=ledger["snapshot_rows"],
                eligible_rows=ledger["eligible_rows"],
                page_sequence=ledger["completed_pages"],
                previous_ack_sha256=ledger["last_ack_sha256"],
                cursor=ledger["cursor"],
                committed_digests=set(ledger["committed_digests"]),
                selection_exhausted=summary.get("selection_exhausted"),
            )
        except (TypeError, ValueError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 pending page does not replay against its ack chain",
                stage="stage2_sector_audit",
            ) from exc
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

    def _certificate_requires_retry(self, result: Mapping[str, Any]) -> bool:
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
            # A summary-side disposition is not proof. Resolve the fixed
            # per-digest certificate and cache metadata, then replay its typed
            # final-gate classification before permitting a terminal rejection.
            digest = result.get("canonical_digest")
            path_value = certificate.get("certificate_path")
            if (
                not isinstance(digest, str)
                or not digest
                or not isinstance(path_value, str)
                or not path_value
            ):
                return True
            token = hashlib.sha256(digest.encode()).hexdigest()
            expected_path = (
                self.paths.solver_state
                / "certificates"
                / f"{token}.json"
            ).resolve()
            expected_metadata = expected_path.with_name(
                f"{token}.cache.json",
            )
            try:
                path = _resolve_path(path_value, self.config.repo_dir).resolve()
                path.relative_to(self.paths.solver_state.resolve())
                if path != expected_path:
                    return True
                artifact = _read_json_object(path)
                metadata = _read_json_object(expected_metadata)
                artifact_sha256 = artifact.get("certificate_sha256")
                known_answer_sha256 = _file_sha256(
                    self.config.known_answer_artifact,
                )
                artifact_known_answer = artifact.get("known_answer")
                if (
                    not isinstance(artifact_sha256, str)
                    or artifact_sha256 != _certificate_sha256(artifact)
                    or certificate.get("certificate_sha256")
                    != artifact_sha256
                    or certificate.get("failure_disposition")
                    != artifact.get("failure_disposition")
                    or not isinstance(artifact_known_answer, Mapping)
                    or artifact_known_answer.get("artifact_sha256")
                    != known_answer_sha256
                    or metadata.get("schema_version")
                    != CERTIFICATE_CACHE_SCHEMA_VERSION
                    or metadata.get("kind") != "qldpc-certificate-cache"
                    or metadata.get("canonical_digest") != digest
                    or metadata.get("known_answer_sha256")
                    != known_answer_sha256
                    or metadata.get("certificate_sha256")
                    != artifact_sha256
                    or metadata.get("certificate_payload_sha256")
                    != _audit_json_sha256(artifact)
                    or metadata.get("exact") is not True
                    or metadata.get("passed") is not False
                ):
                    return True
            except (OSError, TypeError, ValueError, PipelineError):
                return True
            return not terminal_candidate_rejection(artifact)
        return not (
            certificate.get("certificate_passed") is True
            and certificate.get("verification_passed") is True
        )

    def _proof_incompleteness(
        self,
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
        stage2_page = stage2.get("selection_page")
        stage2_scan = (
            stage2_page.get("scan_evidence")
            if isinstance(stage2_page, Mapping)
            else None
        )
        if (
            isinstance(stage2_scan, Mapping)
            and stage2_scan.get("snapshot_rows") == 0
            and stage2_scan.get("eligible_rows") == 0
            and stage2_page.get("start_index") == 0
            and stage2_page.get("next_index") == 0
            and stage2_page.get("selected_digests") == []
            and stage2_scan.get("selection_exhausted") is True
        ):
            add(
                "stage2_sector_audit",
                "Stage 2 ranked candidate pool is empty",
                code="STAGE2_EMPTY_CANDIDATE_POOL",
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
            (
                "structural_unresolved_candidates",
                "Stage 2 structural reconstruction remains retryable",
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
            } and self._certificate_requires_retry(result):
                add(
                    "stage2_sector_audit",
                    "Stage 2 threshold proof has incomplete or unverified certificate",
                    digest,
                    code="STAGE2_CERTIFICATE_INCOMPLETE",
                )
            elif status == "UNRESOLVED" and result.get("retry_required") is True:
                add(
                    "stage2_sector_audit",
                    "Stage 2 compact low-weight gate is UNKNOWN and retryable",
                    digest,
                    code="STAGE2_COMPACT_LOW_WEIGHT_RETRY",
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
                elif escalated.get("status") in {
                    "INELIGIBLE",
                    "BOUND_INSUFFICIENT",
                    "EXACTNESS_GAP",
                }:
                    # These outcomes are terminal for the selected theorem
                    # lane: more time cannot make static hypotheses true,
                    # erase a verified auxiliary witness, or turn a complete
                    # original-code UNSAT decision into the missing exact
                    # witness. None rejects the original code, so retain a
                    # campaign-wide gap without solver-time escalation.
                    gap_status = str(escalated["status"])
                    gap_reason, gap_code = {
                        "INELIGIBLE": (
                            "Stage 3 theorem lane is ineligible for this "
                            "candidate",
                            STAGE3_INELIGIBLE_RESULT_CODE,
                        ),
                        "BOUND_INSUFFICIENT": (
                            "Stage 3 auxiliary bound is insufficient for this "
                            "candidate",
                            STAGE3_BOUND_INSUFFICIENT_RESULT_CODE,
                        ),
                        "EXACTNESS_GAP": (
                            "Stage 3 proved the requested lower bound but lacks "
                            "an exact original-code witness",
                            STAGE3_EXACTNESS_GAP_RESULT_CODE,
                        ),
                    }[gap_status]
                    add(
                        "stage3_direction_audit",
                        gap_reason,
                        digest,
                        code=gap_code,
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
            elif status == "UNSUPPORTED":
                add(
                    "stage2_sector_audit",
                    "Stage 2 candidate has no supported exhaustive audit",
                    digest,
                    code="STAGE2_UNSUPPORTED_RESULT",
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
            elif result.get("status") == "UNSUPPORTED":
                add(
                    "stage3_direction_audit",
                    "Stage 3 candidate has no supported exhaustive audit",
                    digest,
                    code="STAGE3_UNSUPPORTED_RESULT",
                )
            elif (
                result.get("status") in {"THRESHOLD_PROVEN", "EXACT_PROVEN"}
                and self._certificate_requires_retry(result)
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
        """Carry campaign-wide diagnostics and proof gaps across pages."""

        page = stage2.get("selection_page")
        if not isinstance(page, Mapping):
            return dict(incompleteness)
        binding = page.get("binding_sha256")
        if not isinstance(binding, str):
            return dict(incompleteness)

        pagination = self.state.setdefault("stage2_pagination", {})
        persisted: list[Mapping[str, Any]] = []
        if pagination.get("binding_sha256") == binding:
            raw_persisted = pagination.get(
                "paginated_persistent_incompleteness",
            )
            if not isinstance(raw_persisted, list):
                # Read the two explicit legacy/diagnostic views when resuming
                # state written before the combined fail-closed field existed.
                raw_persisted = [
                    *(
                        pagination.get("global_input_incompleteness", [])
                        if isinstance(
                            pagination.get("global_input_incompleteness"),
                            list,
                        )
                        else []
                    ),
                    *(
                        pagination.get("coverage_gap_incompleteness", [])
                        if isinstance(
                            pagination.get("coverage_gap_incompleteness"),
                            list,
                        )
                        else []
                    ),
                ]
            persisted = [
                reason
                for reason in raw_persisted
                if isinstance(reason, Mapping)
                and reason.get("code")
                in PAGINATED_PERSISTENT_INCOMPLETENESS_CODES
            ]
        else:
            for field in (
                "paginated_persistent_incompleteness",
                "global_input_incompleteness",
                "coverage_gap_incompleteness",
            ):
                pagination.pop(field, None)

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
            if (
                stage == "stage2_sector_audit"
                and stage_reasons
                and all(
                    reason.get("code")
                    in STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES
                    for reason in stage_reasons
                )
            ):
                # A terminal input diagnostic is durable evidence, not a
                # retryable solver result.  Keep the Stage 2 machine cache
                # reusable so an unchanged resume validates and reuses the
                # same sealed pending page.  Any command, source, input, or
                # ledger-prestate change still invalidates that cache through
                # the normal _execute_stage checks.
                continue
            record["status"] = "INCOMPLETE"
            record["machine_status"] = "INCOMPLETE"
            record["incomplete_at"] = utc_now()
            record["incomplete_reasons"] = stage_reasons
        self._write_state()

    @staticmethod
    def _deferred_page_hash(entry: Mapping[str, Any]) -> str:
        unsigned = dict(entry)
        unsigned.pop("entry_sha256", None)
        return _canonical_sha256(unsigned)

    @staticmethod
    def _validated_stage2_selection_ledger(
        ledger: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Replay the complete cursor/ack chain and progress seal."""

        try:
            return validate_selection_ledger(
                ledger,
                binding_sha256=str(ledger.get("binding_sha256")),
                snapshot_identity_sha256_value=str(
                    ledger.get("snapshot_identity_sha256")
                ),
                snapshot_rows=ledger.get("snapshot_rows"),  # type: ignore[arg-type]
                eligible_rows=ledger.get("eligible_rows"),  # type: ignore[arg-type]
            )
        except (TypeError, ValueError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 selection ledger progress seal does not replay",
                stage="stage2_sector_audit",
            ) from exc

    def _validate_deferred_stage2_pages(
        self,
        ledger: Mapping[str, Any],
    ) -> list[dict[str, Any]]:
        """Replay every parked page and its immutable evidence manifest."""

        ledger = self._validated_stage2_selection_ledger(ledger)
        raw_pages = ledger.get("deferred_pages", [])
        if not isinstance(raw_pages, list):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 selection ledger has an invalid deferred page list",
                stage="stage2_sector_audit",
            )
        binding_sha256 = ledger.get("binding_sha256")
        committed = ledger.get("committed_digests")
        cursor = ledger.get("cursor")
        completed_pages = ledger.get("completed_pages")
        if (
            not isinstance(binding_sha256, str)
            or not isinstance(committed, list)
            or any(
                not isinstance(digest, str) or not digest
                for digest in committed
            )
            or len(set(committed)) != len(committed)
            or isinstance(cursor, bool)
            or not isinstance(cursor, int)
            or cursor < 0
            or isinstance(completed_pages, bool)
            or not isinstance(completed_pages, int)
            or completed_pages < len(raw_pages)
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 selection ledger cannot bind deferred pages",
                stage="stage2_sector_audit",
            )
        committed_set = set(committed)
        deferred_ack_pages = {
            str(ack.get("page_sha256")): dict(ack.get("page"))
            for ack in ledger["ack_chain"]
            if (
                isinstance(ack, Mapping)
                and ack.get("disposition") == "DEFERRED"
                and isinstance(ack.get("page"), Mapping)
            )
        }
        pages: list[dict[str, Any]] = []
        seen_pages: set[str] = set()
        seen_digests: set[str] = set()
        previous_start_index = -1
        solver_root = self.paths.solver_state.resolve(strict=True)
        for raw_entry in raw_pages:
            if not isinstance(raw_entry, Mapping):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 deferred page entry is not an object",
                    stage="stage2_sector_audit",
                )
            entry = dict(raw_entry)
            page = entry.get("page")
            selected = entry.get("selected_digests")
            page_sha256 = entry.get("page_sha256")
            if (
                entry.get("schema_version")
                != STAGE2_DEFERRED_PAGE_SCHEMA_VERSION
                or entry.get("gate") != STAGE2_DEFERRED_PAGE_GATE
                or entry.get("binding_sha256") != binding_sha256
                or not isinstance(page, Mapping)
                or not isinstance(page_sha256, str)
                or not isinstance(entry.get("selection_exhausted"), bool)
                or page.get("page_sha256") != page_sha256
                or not isinstance(selected, list)
                or not selected
                or selected != page.get("selected_digests")
                or any(
                    not isinstance(digest, str) or not digest
                    for digest in selected
                )
                or len(set(selected)) != len(selected)
                or entry.get("entry_sha256")
                != self._deferred_page_hash(entry)
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 deferred page entry does not replay",
                    stage="stage2_sector_audit",
                )
            start_index = page.get("start_index")
            next_index = page.get("next_index")
            if (
                page.get("binding_sha256") != binding_sha256
                or isinstance(start_index, bool)
                or not isinstance(start_index, int)
                or start_index < 0
                or isinstance(next_index, bool)
                or not isinstance(next_index, int)
                or next_index <= start_index
                or next_index > cursor
                or start_index <= previous_start_index
                or deferred_ack_pages.get(page_sha256) != dict(page)
                or page_sha256 in seen_pages
                or seen_digests.intersection(selected)
                or not set(selected).issubset(committed_set)
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 deferred page binding/digests are inconsistent",
                    stage="stage2_sector_audit",
                )
            expected_manifest_relative = (
                f"deferred-pages/{page_sha256}/manifest.json"
            )
            if entry.get("manifest_path") != expected_manifest_relative:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 deferred page manifest path is not canonical",
                    stage="stage2_sector_audit",
                )
            manifest_path = (
                self.paths.solver_state / expected_manifest_relative
            )
            manifest = _read_json_object(manifest_path)
            unsigned_manifest = dict(manifest)
            manifest_sha256 = unsigned_manifest.pop("manifest_sha256", None)
            manifest_incompleteness = manifest.get("proof_incompleteness")
            manifest_active = manifest.get("proof_retry_active")
            if (
                manifest.get("schema_version")
                != STAGE2_DEFERRED_PAGE_SCHEMA_VERSION
                or manifest.get("gate") != STAGE2_DEFERRED_PAGE_GATE
                or manifest.get("page") != dict(page)
                or manifest.get("selected_digests") != selected
                or manifest.get("selection_exhausted")
                != entry.get("selection_exhausted")
                or manifest.get("proof_incompleteness_sha256")
                != entry.get("proof_incompleteness_sha256")
                or not isinstance(manifest_incompleteness, Mapping)
                or _canonical_sha256(manifest_incompleteness)
                != manifest.get("proof_incompleteness_sha256")
                or manifest.get("controller_binding_sha256")
                != entry.get("controller_binding_sha256")
                or manifest.get("controller_active_sha256")
                != entry.get("controller_active_sha256")
                or not isinstance(manifest_active, Mapping)
                or _canonical_sha256(manifest_active)
                != manifest.get("controller_active_sha256")
                or not isinstance(manifest_sha256, str)
                or manifest_sha256 != _canonical_sha256(unsigned_manifest)
                or entry.get("manifest_sha256") != _file_sha256(manifest_path)
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 deferred page manifest does not replay",
                    stage="stage2_sector_audit",
                )
            artifacts = manifest.get("artifacts")
            if not isinstance(artifacts, Mapping):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 deferred page lacks artifact hashes",
                    stage="stage2_sector_audit",
                )
            for metadata in artifacts.values():
                if not isinstance(metadata, Mapping):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "Stage 2 deferred artifact metadata is malformed",
                        stage="stage2_sector_audit",
                    )
                archived_path = metadata.get("archived_path")
                expected_sha256 = metadata.get("sha256")
                if not isinstance(expected_sha256, str):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "Stage 2 deferred artifact lacks a hash",
                        stage="stage2_sector_audit",
                    )
                if archived_path is None:
                    continue
                if not isinstance(archived_path, str):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "Stage 2 deferred artifact path is malformed",
                        stage="stage2_sector_audit",
                    )
                archived = (
                    self.paths.solver_state / archived_path
                ).resolve(strict=True)
                try:
                    archived.relative_to(solver_root)
                except ValueError as exc:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "Stage 2 deferred artifact escapes solver state",
                        stage="stage2_sector_audit",
                    ) from exc
                if _file_sha256(archived) != expected_sha256:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "Stage 2 deferred artifact hash does not replay",
                        stage="stage2_sector_audit",
                    )
            seen_pages.add(page_sha256)
            seen_digests.update(selected)
            previous_start_index = start_index
            pages.append(entry)
        return pages

    def _archive_deferred_stage2_page(
        self,
        *,
        page: Mapping[str, Any],
        selection_exhausted: bool,
        incompleteness: Mapping[str, Any],
        active: Mapping[str, Any],
    ) -> tuple[str, str]:
        """Persist the complete proof-page evidence before moving its cursor."""

        page_sha256 = str(page["page_sha256"])
        relative_root = Path("deferred-pages") / page_sha256
        archive_root = _reject_symlink_components(
            self.paths.solver_state / relative_root,
            classification="UNSAFE_CONTROL_PATH",
            label="deferred proof page archive",
        )
        archive_root.mkdir(mode=0o700, parents=True, exist_ok=True)
        self._ensure_solver_state_tree_safe()
        manifest_path = archive_root / "manifest.json"
        expected_incompleteness_sha256 = _canonical_sha256(incompleteness)
        expected_active_sha256 = _canonical_sha256(active)
        if manifest_path.is_file():
            # PREPARE is deliberately idempotent. A crash before the ledger
            # rename may update live state during restart; the already-written
            # immutable archive remains authoritative for this exact page.
            manifest = _read_json_object(manifest_path)
            unsigned_manifest = dict(manifest)
            embedded_manifest_sha256 = unsigned_manifest.pop(
                "manifest_sha256", None
            )
            if (
                manifest.get("schema_version")
                != STAGE2_DEFERRED_PAGE_SCHEMA_VERSION
                or manifest.get("gate") != STAGE2_DEFERRED_PAGE_GATE
                or manifest.get("page") != dict(page)
                or manifest.get("selected_digests")
                != list(page["selected_digests"])
                or manifest.get("selection_exhausted")
                is not selection_exhausted
                or manifest.get("proof_incompleteness_sha256")
                != expected_incompleteness_sha256
                or manifest.get("controller_binding_sha256")
                != active.get("binding_sha256")
                or manifest.get("controller_active_sha256")
                != expected_active_sha256
                or embedded_manifest_sha256
                != _canonical_sha256(unsigned_manifest)
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "existing deferred proof page PREPARE does not replay",
                    stage="stage2_sector_audit",
                )
            archived_artifacts = manifest.get("artifacts")
            if not isinstance(archived_artifacts, Mapping):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "existing deferred proof page PREPARE lacks artifacts",
                    stage="stage2_sector_audit",
                )
            solver_root = self.paths.solver_state.resolve(strict=True)
            for metadata in archived_artifacts.values():
                if not isinstance(metadata, Mapping):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "deferred PREPARE artifact metadata is malformed",
                        stage="stage2_sector_audit",
                    )
                archived_path = metadata.get("archived_path")
                expected_sha256 = metadata.get("sha256")
                if archived_path is None:
                    continue
                if not isinstance(archived_path, str) or not isinstance(
                    expected_sha256, str
                ):
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "deferred PREPARE artifact binding is malformed",
                        stage="stage2_sector_audit",
                    )
                archived = (
                    self.paths.solver_state / archived_path
                ).resolve(strict=True)
                try:
                    archived.relative_to(solver_root)
                except ValueError as exc:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "deferred PREPARE artifact escapes solver state",
                        stage="stage2_sector_audit",
                    ) from exc
                if _file_sha256(archived) != expected_sha256:
                    raise PipelineError(
                        "OUTPUT_INVALID",
                        "deferred PREPARE artifact hash does not replay",
                        stage="stage2_sector_audit",
                    )
            return (
                (relative_root / "manifest.json").as_posix(),
                _file_sha256(manifest_path),
            )

        # Ranked files may contain the entire campaign pool and can be very
        # large. Their hashes are retained, while the page-local summaries,
        # certificates, and strict outcome are copied into the durable archive.
        sources: tuple[tuple[str, Path, bool], ...] = (
            ("stage2_ranked", self.paths.stage2_ranked, False),
            ("stage2_summary", self.paths.stage2_summary, True),
            ("stage3_ranked", self.paths.stage3_ranked, False),
            ("stage3_summary", self.paths.stage3_summary, True),
            ("stage3_thresholds", self.paths.stage3_thresholds, True),
            ("stage4_certificates", self.paths.stage4_certificates, True),
            ("stage4_summary", self.paths.stage4_summary, True),
            ("stage5_gate", self.paths.stage5_gate, True),
            ("stage5_incomplete", self.paths.stage5_incomplete, True),
            ("stage5_no_win", self.paths.stage5_no_win, True),
            (
                "selection_ledger",
                self.paths.stage2_selection_ledger,
                True,
            ),
            (
                "proof_retry_controller",
                self.paths.proof_retry_controller,
                True,
            ),
        )
        artifacts: dict[str, dict[str, Any]] = {}
        for label, source, should_copy in sources:
            hashes = _hash_paths(
                [source],
                require=False,
                classification="UNSAFE_CONTROL_PATH",
                label=f"deferred {label}",
            )
            source_sha256 = hashes[str(_lexical_absolute(source))]
            if source_sha256 is None:
                continue
            archived_relative: str | None = None
            if should_copy:
                destination = archive_root / f"{label}{source.suffix}"
                _atomic_write_text(destination, source.read_text())
                if (
                    _file_sha256(destination) != source_sha256
                    or _file_sha256(source) != source_sha256
                ):
                    raise PipelineError(
                        "INPUT_CHANGED_DURING_STAGE",
                        f"{label} changed while parking a deferred proof page",
                        stage="stage2_sector_audit",
                    )
                archived_relative = (
                    relative_root / destination.name
                ).as_posix()
            artifacts[label] = {
                "source_path": str(source),
                "archived_path": archived_relative,
                "sha256": source_sha256,
            }

        manifest_payload = {
            "schema_version": STAGE2_DEFERRED_PAGE_SCHEMA_VERSION,
            "gate": STAGE2_DEFERRED_PAGE_GATE,
            "page": dict(page),
            "selected_digests": list(page["selected_digests"]),
            "selection_exhausted": selection_exhausted,
            "proof_incompleteness": dict(incompleteness),
            "proof_incompleteness_sha256": (
                expected_incompleteness_sha256
            ),
            "proof_retry_active": dict(active),
            "controller_binding_sha256": active.get("binding_sha256"),
            "controller_active_sha256": expected_active_sha256,
            "controller_file_sha256": _file_sha256(
                self.paths.proof_retry_controller
            ),
            "artifacts": artifacts,
        }
        manifest = {
            **manifest_payload,
            "manifest_sha256": _canonical_sha256(manifest_payload),
        }
        atomic_write_json(manifest_path, manifest)
        self._ensure_solver_state_tree_safe()
        return (
            (relative_root / "manifest.json").as_posix(),
            _file_sha256(manifest_path),
        )

    def _defer_capped_stage2_page(
        self,
        controller: dict[str, Any],
        active: dict[str, Any],
        reason: str,
    ) -> tuple[bool, bool]:
        """Atomically park a capped page and advance to later candidates.

        Returns ``(deferred, has_later_page)``. Legacy, unpaginated runs return
        ``(False, False)`` and retain the old explicit capped state.
        """

        if not self.paths.stage2_summary.is_file():
            return False, False
        summary = _read_json_object(self.paths.stage2_summary)
        page = summary.get("selection_page")
        if not isinstance(page, Mapping):
            return False, False
        result = self.state.get("result")
        incompleteness = (
            result.get("proof_incompleteness")
            if isinstance(result, Mapping)
            else None
        )
        if (
            self.state.get("status") != "INCOMPLETE"
            or not isinstance(incompleteness, Mapping)
            or not self._proof_retry_eligible(incompleteness)
        ):
            return False, False
        selection_exhausted = summary.get("selection_exhausted")
        if not isinstance(selection_exhausted, bool):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 deferred page lacks selection exhaustion status",
                stage="stage2_sector_audit",
            )

        if active.get("status") == "CAPPED":
            if active.get("cap_reason") != reason:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "proof retry cap reason changed before page deferral",
                    stage="stage2_sector_audit",
                )
        else:
            active.update(
                {
                    "status": "CAPPED",
                    "cap_reason": reason,
                    "capped_at": utc_now(),
                }
            )
            controller["active"] = active
            self._write_proof_retry_controller(controller)

        manifest_path, manifest_sha256 = (
            self._archive_deferred_stage2_page(
                page=page,
                selection_exhausted=selection_exhausted,
                incompleteness=incompleteness,
                active=active,
            )
        )
        self._ensure_solver_state_tree_safe()
        ledger = self._validated_stage2_selection_ledger(
            _read_json_object(self.paths.stage2_selection_ledger)
        )
        if (
            ledger.get("binding_sha256") != page.get("binding_sha256")
            or ledger.get("pending") != dict(page)
            or ledger.get("cursor") != page.get("start_index")
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 capped page does not match its selection ledger",
                stage="stage2_sector_audit",
            )
        self._validate_deferred_stage2_pages(ledger)
        selected_digests = page.get("selected_digests")
        start_index = page.get("start_index")
        next_index = page.get("next_index")
        committed = ledger.get("committed_digests")
        completed_pages = ledger.get("completed_pages")
        try:
            validate_selection_page(
                page,
                binding_sha256=ledger["binding_sha256"],
                snapshot_identity_sha256_value=ledger[
                    "snapshot_identity_sha256"
                ],
                snapshot_rows=ledger["snapshot_rows"],
                eligible_rows=ledger["eligible_rows"],
                page_sequence=ledger["completed_pages"],
                previous_ack_sha256=ledger["last_ack_sha256"],
                cursor=ledger["cursor"],
                committed_digests=set(ledger["committed_digests"]),
                selection_exhausted=selection_exhausted,
            )
        except (TypeError, ValueError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                "capped Stage 2 page scan evidence does not replay",
                stage="stage2_sector_audit",
            ) from exc
        if (
            not isinstance(selected_digests, list)
            or not selected_digests
            or isinstance(start_index, bool)
            or not isinstance(start_index, int)
            or isinstance(next_index, bool)
            or not isinstance(next_index, int)
            or next_index <= start_index
            or not isinstance(committed, list)
            or set(committed).intersection(selected_digests)
            or isinstance(completed_pages, bool)
            or not isinstance(completed_pages, int)
            or completed_pages < 0
        ):
            raise PipelineError(
                "NO_PAGINATION_PROGRESS",
                "capped Stage 2 page cannot advance its durable cursor",
                stage="stage2_sector_audit",
            )
        entry_payload = {
            "schema_version": STAGE2_DEFERRED_PAGE_SCHEMA_VERSION,
            "gate": STAGE2_DEFERRED_PAGE_GATE,
            "binding_sha256": page["binding_sha256"],
            "page_sha256": page["page_sha256"],
            "page": dict(page),
            "selected_digests": list(selected_digests),
            "selection_exhausted": selection_exhausted,
            "cap_reason": reason,
            "proof_incompleteness_sha256": _canonical_sha256(
                incompleteness
            ),
            "controller_binding_sha256": active["binding_sha256"],
            "controller_active_sha256": _canonical_sha256(active),
            "manifest_path": manifest_path,
            "manifest_sha256": manifest_sha256,
            "deferred_at": utc_now(),
        }
        entry = {
            **entry_payload,
            "entry_sha256": _canonical_sha256(entry_payload),
        }
        try:
            updated = acknowledge_selection_page(
                ledger,
                page,
                disposition="DEFERRED",
                deferred_entry=entry,
            )
        except (TypeError, ValueError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 deferred acknowledgement chain rejected its page",
                stage="stage2_sector_audit",
            ) from exc
        updated["last_acknowledged_page_sha256"] = page["page_sha256"]
        updated["last_acknowledged_at"] = utc_now()
        updated = seal_selection_ledger(updated)
        # This is the transaction boundary: cursor movement and durable
        # deferred evidence become visible in the same atomic replacement.
        atomic_write_json(self.paths.stage2_selection_ledger, updated)
        self._ensure_solver_state_tree_safe()

        active.update(
            {
                "status": "DEFERRED",
                "deferred_page_sha256": page["page_sha256"],
                "deferred_at": utc_now(),
            }
        )
        controller["active"] = active
        self._write_proof_retry_controller(controller)
        public = {
            "binding_sha256": active["binding_sha256"],
            "status": "DEFERRED",
            "cap_reason": reason,
            "attempts": len(active.get("attempts", [])),
            "elapsed_seconds": active.get("elapsed_seconds", 0),
            "deferred_page_sha256": page["page_sha256"],
            "controller_path": str(self.paths.proof_retry_controller),
        }
        self.state["proof_retry"] = public
        deferred_incompleteness = (
            self._carry_deferred_stage2_incompleteness(incompleteness)
        )
        pagination = self.state.setdefault("stage2_pagination", {})
        pagination.update(
            {
                "binding_sha256": page["binding_sha256"],
                "cursor": next_index,
                "completed_pages": updated["completed_pages"],
                "deferred_pages": len(updated["deferred_pages"]),
                "selection_exhausted": selection_exhausted,
                "last_page_sha256": page["page_sha256"],
                "last_advanced_at": utc_now(),
            }
        )
        if isinstance(result, dict):
            result["proof_retry"] = public
            result["proof_incompleteness"] = deferred_incompleteness
        self._write_state()
        return True, not selection_exhausted

    def _carry_deferred_stage2_incompleteness(
        self,
        incompleteness: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Make a deferred backlog permanently block a false NO_WIN."""

        if not self.paths.stage2_selection_ledger.is_file():
            return dict(incompleteness)
        ledger = _read_json_object(self.paths.stage2_selection_ledger)
        pages = self._validate_deferred_stage2_pages(ledger)
        if not pages:
            return dict(incompleteness)
        reasons = [
            dict(reason)
            for reason in incompleteness.get("reasons", [])
            if isinstance(reason, Mapping)
        ]
        reason = {
            "stage": "stage2_sector_audit",
            "reason": (
                f"{len(pages)} Stage 2 proof page(s) exhausted their bounded "
                "retry budgets and remain deferred"
            ),
            "code": STAGE2_DEFERRED_PAGE_CODE,
            "deferred_pages": len(pages),
            "deferred_candidates": sum(
                len(page["selected_digests"]) for page in pages
            ),
            "deferred_page_digests_sha256": _canonical_sha256(
                [page["page_sha256"] for page in pages]
            ),
        }
        if not any(
            existing.get("code") == STAGE2_DEFERRED_PAGE_CODE
            for existing in reasons
        ):
            reasons.append(reason)
        retry_stages = {
            str(stage)
            for stage in incompleteness.get("retry_stages", [])
            if stage in STAGE_ORDER
        }
        retry_stages.add("stage2_sector_audit")
        return {
            "incomplete": True,
            "reasons": reasons,
            "retry_stages": [
                stage for stage in STAGE_ORDER if stage in retry_stages
            ],
        }

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
        summary = _read_json_object(self.paths.stage2_summary)
        page = summary.get("selection_page")
        # Old runs did not have a durable page. Returning INCOMPLETE is safer
        # than guessing a cursor and preserves backwards compatibility.
        if not isinstance(page, Mapping):
            return False
        selection_exhausted = summary.get("selection_exhausted")
        if not isinstance(selection_exhausted, bool):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 page lacks selection exhaustion status",
                stage="stage2_sector_audit",
            )
        codes = [
            reason.get("code")
            for reason in reasons
            if isinstance(reason, Mapping)
        ]
        carry_codes = {
            *PAGINATED_PERSISTENT_INCOMPLETENESS_CODES,
            STAGE2_DEFERRED_PAGE_CODE,
            STAGE2_STRUCTURAL_UNRESOLVED_CODE,
        }
        if len(codes) != len(reasons):
            return False
        if selection_exhausted:
            # Terminal diagnostic pages remain pending. Their page/scan seal
            # is the replay anchor on later resumes.
            if not codes or any(code not in carry_codes for code in codes):
                return False
        elif (
            "STAGE2_SELECTION_TRUNCATED" not in codes
            or any(
                code != "STAGE2_SELECTION_TRUNCATED"
                and code not in carry_codes
                for code in codes
            )
        ):
            return False
        self._ensure_solver_state_tree_safe()
        ledger = self._validated_stage2_selection_ledger(
            _read_json_object(self.paths.stage2_selection_ledger)
        )
        if (
            ledger.get("binding_sha256") != page.get("binding_sha256")
            or ledger.get("pending") != dict(page)
            or ledger.get("cursor") != page.get("start_index")
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 selection ledger does not match its pending page",
                stage="stage2_sector_audit",
            )
        self._validate_deferred_stage2_pages(ledger)
        start_index = page.get("start_index")
        next_index = page.get("next_index")
        selected_digests = page.get("selected_digests")
        committed = ledger.get("committed_digests")
        completed_pages = ledger.get("completed_pages")
        try:
            validate_selection_page(
                page,
                binding_sha256=ledger["binding_sha256"],
                snapshot_identity_sha256_value=ledger[
                    "snapshot_identity_sha256"
                ],
                snapshot_rows=ledger["snapshot_rows"],
                eligible_rows=ledger["eligible_rows"],
                page_sequence=ledger["completed_pages"],
                previous_ack_sha256=ledger["last_ack_sha256"],
                cursor=ledger["cursor"],
                committed_digests=set(ledger["committed_digests"]),
                selection_exhausted=selection_exhausted,
            )
        except (TypeError, ValueError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 pending page scan evidence does not replay",
                stage="stage2_sector_audit",
            ) from exc
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
        terminal_root = bool(
            ledger["eligible_rows"] == 0
            and start_index == 0
            and next_index == 0
            and selected_digests == []
            and selection_exhausted
        )
        if next_index <= start_index and not terminal_root:
            self.state.setdefault("stage2_pagination", {}).update({
                "no_progress": True,
                "cursor": start_index,
                "pending_page_sha256": page.get("page_sha256"),
                "detected_at": utc_now(),
            })
            self._write_state()
            raise PipelineError(
                "NO_PAGINATION_PROGRESS",
                "Stage 2 page did not advance its finite candidate cursor",
                stage="stage2_sector_audit",
            )

        persistent_incompleteness = [
            dict(reason)
            for reason in reasons
            if (
                isinstance(reason, Mapping)
                and reason.get("code")
                in PAGINATED_PERSISTENT_INCOMPLETENESS_CODES
            )
        ]
        # Persist the fail-closed diagnostic before acknowledging the page. If
        # the ledger write is interrupted, replaying the same pending page can
        # only duplicate (and later deduplicate) this evidence.
        pagination = self.state.setdefault("stage2_pagination", {})
        if pagination.get("binding_sha256") == page["binding_sha256"]:
            raw_previous = pagination.get(
                "paginated_persistent_incompleteness", []
            )
            if isinstance(raw_previous, list):
                seen_persistent = {
                    _canonical_sha256(reason)
                    for reason in persistent_incompleteness
                }
                for previous in raw_previous:
                    if (
                        not isinstance(previous, Mapping)
                        or previous.get("code")
                        not in PAGINATED_PERSISTENT_INCOMPLETENESS_CODES
                    ):
                        continue
                    item = dict(previous)
                    digest = _canonical_sha256(item)
                    if digest not in seen_persistent:
                        seen_persistent.add(digest)
                        persistent_incompleteness.append(item)
        global_input_incompleteness = [
            reason
            for reason in persistent_incompleteness
            if reason.get("code") in STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES
        ]
        coverage_gap_incompleteness = [
            reason
            for reason in persistent_incompleteness
            if reason.get("code")
            in PAGINATED_COVERAGE_GAP_INCOMPLETENESS_CODES
        ]
        pagination.update({
            "binding_sha256": page["binding_sha256"],
            "paginated_persistent_incompleteness": (
                persistent_incompleteness
            ),
            "global_input_incompleteness": global_input_incompleteness,
            "coverage_gap_incompleteness": coverage_gap_incompleteness,
            "pending_page_sha256": page["page_sha256"],
        })
        self._write_state()
        if selection_exhausted:
            stage2_record = self.state["stages"]["stage2_sector_audit"]
            cached_config = stage2_record.get("stage_config")
            cached_command = stage2_record.get("command")
            if not isinstance(cached_config, Mapping) or not isinstance(
                cached_command, list
            ):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 terminal page lacks reusable cache provenance",
                    stage="stage2_sector_audit",
                )
            # The CLI transaction installed this terminal pending page after
            # _execute_stage captured its prestate. Rebase only that cache
            # component to the now-stable sealed ledger. An unchanged resume
            # can then validate/reuse the diagnostic, while ordinary source,
            # command, candidate-input and output hashes still invalidate it.
            rebased_config = dict(cached_config)
            rebased_config["selection_ledger_prestate_sha256"] = (
                self._stage2_selection_ledger_prestate_sha256()
            )
            stage2_record["stage_config"] = rebased_config
            stage2_record["stage_fingerprint"] = (
                self._stage_config_fingerprint(
                    cached_command,
                    rebased_config,
                )
            )
            pagination.update({
                "cursor": start_index,
                "completed_pages": ledger["completed_pages"],
                "selection_exhausted": True,
                "last_page_sha256": page["page_sha256"],
                "terminal_pending": True,
                "last_advanced_at": utc_now(),
            })
            self._write_state()
            return False

        try:
            updated = acknowledge_selection_page(
                ledger,
                page,
                disposition="COMPLETED",
            )
        except (TypeError, ValueError) as exc:
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 acknowledgement chain rejected its pending page",
                stage="stage2_sector_audit",
            ) from exc
        updated["last_acknowledged_page_sha256"] = page["page_sha256"]
        updated["last_acknowledged_at"] = utc_now()
        updated = seal_selection_ledger(updated)
        atomic_write_json(self.paths.stage2_selection_ledger, updated)
        self._ensure_solver_state_tree_safe()

        pagination.update({
            "binding_sha256": page["binding_sha256"],
            "cursor": next_index,
            "completed_pages": updated["completed_pages"],
            "selection_exhausted": selection_exhausted,
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
            sector_sat = (
                certificate.get("certificate_type")
                == SECTOR_SAT_CERTIFICATE_TYPE
            )
            twobga = (
                certificate.get("certificate_type")
                == TWOBGA_CERTIFICATE_TYPE
            )
            try:
                if twobga:
                    twobga_exact = certificate.get("twobga_exact")
                    proof = (
                        claim.get("exact_distance_proof")
                        if isinstance(claim, Mapping) else None
                    )
                    exact = bool(
                        "milp" not in certificate
                        and "sector_exact" not in certificate
                        and isinstance(claim, Mapping)
                        and isinstance(twobga_exact, Mapping)
                        and isinstance(proof, Mapping)
                        and not isinstance(claim.get("k"), bool)
                        and isinstance(claim.get("k"), int)
                        and claim["k"] > 0
                        and not isinstance(claim.get("d"), bool)
                        and isinstance(claim.get("d"), int)
                        and claim["d"] > 0
                        and twobga_exact.get("exact") is True
                        and twobga_exact.get("distance") == claim["d"]
                        and twobga_exact.get("lower_bound") == claim["d"]
                        and twobga_exact.get("upper_bound") == claim["d"]
                        and twobga_exact.get("expected_lower_decisions") == 2
                        and twobga_exact.get("completed_lower_decisions") == 2
                        and proof.get("proof_type")
                        == "qldpc-css-twobga-subsystem-exact-proof-v1"
                        and proof.get("exact") is True
                        and proof.get("distance") == claim["d"]
                    )
                elif sector_sat:
                    sector_exact = certificate.get("sector_exact")
                    proof = (
                        claim.get("exact_distance_proof")
                        if isinstance(claim, Mapping) else None
                    )
                    exact = bool(
                        "milp" not in certificate
                        and isinstance(claim, Mapping)
                        and isinstance(sector_exact, Mapping)
                        and isinstance(proof, Mapping)
                        and not isinstance(claim.get("k"), bool)
                        and isinstance(claim.get("k"), int)
                        and claim["k"] > 0
                        and not isinstance(claim.get("d"), bool)
                        and isinstance(claim.get("d"), int)
                        and claim["d"] > 0
                        and sector_exact.get("exact") is True
                        and sector_exact.get("distance") == claim["d"]
                        and sector_exact.get("lower_bound") == claim["d"]
                        and sector_exact.get("upper_bound") == claim["d"]
                        and isinstance(
                            sector_exact.get("expected_lower_decisions"), int,
                        )
                        and not isinstance(
                            sector_exact.get("expected_lower_decisions"), bool,
                        )
                        and sector_exact["expected_lower_decisions"] > 0
                        and sector_exact.get("completed_lower_decisions")
                        == sector_exact["expected_lower_decisions"]
                        and proof.get("proof_type")
                        == "qldpc-css-sector-sat-exact-proof-v1"
                        and proof.get("exact") is True
                        and proof.get("distance") == claim["d"]
                    )
                else:
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
                verification_envelope.get("schema_version")
                == CERTIFICATE_CACHE_SCHEMA_VERSION
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
            if sector_sat and _sector_sat_expected_lower_decisions(
                certificate,
                replay_checks=verification.get("checks"),
                replay_result=verification,
            ) is None:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "sector-SAT certificate does not bind its reduced coverage "
                    f"to a fresh X/Z-isometry replay: {path}",
                    stage="stage4_certificate_merge",
                )
            if twobga and _twobga_expected_lower_decisions(
                certificate,
                replay_checks=verification.get("checks"),
                replay_result=verification,
            ) is None:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "2BGA certificate does not bind both dressed auxiliary "
                    f"sectors to a fresh independent replay: {path}",
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

    def _strict_command(self, *, effective_resume: bool | None = None) -> list[str]:
        if effective_resume is None:
            effective_resume = self.config.resume or self._proof_retry_resume
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
            "--resume" if effective_resume else "--no-resume",
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
        )
        if (
            outcome != expected_outcome
            or value.get("passed") is not (expected_outcome == "WIN")
            or rejected != 0
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
            sector_sat = (
                certificate.get("certificate_type")
                == SECTOR_SAT_CERTIFICATE_TYPE
            )
            twobga = (
                certificate.get("certificate_type")
                == TWOBGA_CERTIFICATE_TYPE
            )
            required_replay_checks = (
                TWOBGA_STRICT_REPLAY_CHECKS
                if twobga
                else (
                    SECTOR_SAT_STRICT_REPLAY_CHECKS
                    if sector_sat
                    else REQUIRED_STRICT_REPLAY_CHECKS
                )
            )
            if twobga:
                contract_expected = _twobga_expected_lower_decisions(
                    certificate,
                    replay_checks=checks,
                    replay_result=(
                        result if isinstance(result, Mapping) else None
                    ),
                )
                rerun = (
                    result.get("rerun")
                    if isinstance(result, Mapping) else None
                )
                replay_counts_valid = bool(
                    contract_expected == 2
                    and isinstance(rerun, Mapping)
                    and rerun.get("completed_sectors") == 2
                    and rerun.get("expected_sectors") == 2
                    and rerun.get("matches") is True
                    and isinstance(result, Mapping)
                    and "directions_verified" not in result
                    and "directions_total" not in result
                    and "sector_decisions_verified" not in result
                    and "sector_decisions_total" not in result
                    and "milp" not in certificate
                    and "sector_exact" not in certificate
                )
            elif sector_sat:
                sector_exact = certificate.get("sector_exact")
                sector_verified = (
                    result.get("sector_decisions_verified")
                    if isinstance(result, Mapping) else None
                )
                sector_total = (
                    result.get("sector_decisions_total")
                    if isinstance(result, Mapping) else None
                )
                expected_sector_total = (
                    sector_exact.get("expected_lower_decisions")
                    if isinstance(sector_exact, Mapping) else None
                )
                contract_expected = _sector_sat_expected_lower_decisions(
                    certificate,
                    replay_checks=checks,
                    replay_result=result if isinstance(result, Mapping) else None,
                )
                replay_counts_valid = bool(
                    contract_expected is not None
                    and expected_sector_total == contract_expected
                    and isinstance(sector_verified, int)
                    and not isinstance(sector_verified, bool)
                    and isinstance(sector_total, int)
                    and not isinstance(sector_total, bool)
                    and sector_verified == sector_total == contract_expected
                    and isinstance(result, Mapping)
                    and "directions_verified" not in result
                    and "directions_total" not in result
                    and "milp" not in certificate
                )
            else:
                replay_counts_valid = bool(
                    isinstance(k, int)
                    and not isinstance(k, bool)
                    and isinstance(directions_verified, int)
                    and not isinstance(directions_verified, bool)
                    and directions_verified == 2 * k
                    and isinstance(directions_total, int)
                    and not isinstance(directions_total, bool)
                    and directions_total == 2 * k
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
                try:
                    failure_disposition = validate_failure_disposition(
                        result.get("failure_disposition"),
                    )
                except ValueError as exc:
                    raise PipelineError(
                        "STRICT_GATE_REJECTED",
                        f"Stage 5 evaluation[{index}] lacks a typed retry reason",
                        stage="stage5_strict_gate",
                    ) from exc
                failure_status = failure_disposition["status"]
                if (
                    result.get("passed") is not False
                    or not isinstance(failures, list)
                    or not failures
                    or failure_status
                    not in {FAILURE_INCOMPLETE, EVIDENCE_CONTRADICTION}
                    or (
                        failure_status == FAILURE_INCOMPLETE
                        and result.get("replay_complete") is not False
                    )
                    or (
                        failure_status == EVIDENCE_CONTRADICTION
                        and result.get("replay_complete") is not True
                    )
                ):
                    raise PipelineError(
                        "STRICT_GATE_REJECTED",
                        f"Stage 5 evaluation[{index}] incomplete evidence is invalid",
                        stage="stage5_strict_gate",
                    )
            elif disposition == "REJECTED":
                raise PipelineError(
                    "STRICT_GATE_REJECTED",
                    "Stage 5 cannot terminally reject a Stage 4 certificate "
                    f"that already passed build and independent replay: {index}",
                    stage="stage5_strict_gate",
                )
            elif (
                result.get("passed") is not True
                or result.get("replay_complete") is not True
                or not isinstance(result.get("final_gate"), Mapping)
                or result["final_gate"].get("accepted") is not True
                or not isinstance(checks, Mapping)
                or not required_replay_checks.issubset(checks)
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
                or not replay_counts_valid
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

    def _stage1_live_outputs_sha256(self) -> str:
        """Hash the current Stage 1 outputs, not merely their stored claims."""

        record = self.state.get("stages", {}).get("stage1_search", {})
        recorded = record.get("output_hashes")
        if not isinstance(recorded, Mapping):
            return _canonical_sha256({})
        observed: dict[str, str | None] = {}
        for path_text in recorded:
            if not isinstance(path_text, str):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 1 output-hash key is not a path",
                    stage="stage1_search",
                )
            current = _hash_paths(
                [Path(path_text)],
                require=False,
                classification="UNSAFE_OUTPUT_PATH",
                label="Stage 1 live output",
            )
            observed[path_text] = current[str(_lexical_absolute(path_text))]
        return _canonical_sha256(observed)

    def _proof_retry_environment_binding(self) -> dict[str, Any]:
        """Bind a deferred generation to every live dependency it can skip."""

        source = self._audit_source_provenance()
        strict_source = self._strict_source_provenance()
        strict_inputs = _hash_paths(
            [
                self.paths.stage4_certificates,
                self.config.known_answer_artifact,
                self.config.known_answer_trust,
            ],
            require=False,
        )
        return {
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
            "proof_config_sha256": _canonical_sha256(
                self._proof_retry_base_config()
            ),
            "stage1_identity_sha256": _canonical_sha256(
                self._stage1_identity()
            ),
            "stage1_outputs_sha256": self._stage1_live_outputs_sha256(),
            "pipeline_resume": self.config.resume,
        }

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
            "stage3_backend": self.config.stage3_backend,
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
            STAGE2_STRUCTURAL_UNRESOLVED_CODE,
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
            unsigned_page = dict(page)
            page_sha256 = unsigned_page.pop("page_sha256", None)
            if page_sha256 != _canonical_sha256(unsigned_page):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 retry page hash does not replay",
                    stage="stage2_sector_audit",
                )
            selection_binding = page.get("binding_sha256")
            if self.paths.stage2_selection_ledger.is_file():
                ledger = self._validated_stage2_selection_ledger(
                    _read_json_object(
                        self.paths.stage2_selection_ledger
                    )
                )
                if (
                    ledger.get("binding_sha256") != selection_binding
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
        binding = {
            "page_sha256": page_sha256,
            "selection_binding_sha256": selection_binding,
            "selected_digests": selected_digests,
            "candidate_digests_sha256": _canonical_sha256(selected_digests),
            **self._proof_retry_environment_binding(),
        }
        return {
            **binding,
            "binding_sha256": _canonical_sha256(binding),
        }

    @staticmethod
    def _proof_checkpoint_candidate_digest(
        value: Mapping[str, Any],
    ) -> str | None:
        """Extract a candidate digest from the checkpoint's bound payload."""

        def visit(raw: Any) -> str | None:
            if not isinstance(raw, Mapping):
                return None
            digest = raw.get("canonical_digest")
            if isinstance(digest, str) and digest:
                return digest
            for key in (
                "candidate",
                "claim",
                "candidate_identity",
                "triage_identity",
                "proof_binding",
                "binding",
            ):
                nested = visit(raw.get(key))
                if nested is not None:
                    return nested
            return None

        return visit(value)

    @staticmethod
    def _proof_checkpoint_record_counts(
        value: Mapping[str, Any],
        *,
        source_kind: str,
    ) -> dict[str, int]:
        """Classify checkpoint work by mathematical, not process, outcome."""

        candidate = value.get("candidate")
        required = value.get("required_distance")
        if isinstance(required, bool) or not isinstance(required, int):
            required = (
                candidate.get("required_distance")
                if isinstance(candidate, Mapping)
                else None
            )
        if isinstance(required, bool) or not isinstance(required, int):
            required = None

        records: list[Mapping[str, Any]] = []
        raw_direction_results = value.get("direction_results")
        if isinstance(raw_direction_results, Mapping):
            records.extend(
                record
                for record in raw_direction_results.values()
                if isinstance(record, Mapping)
            )
        else:
            for key in ("directions", "sectors", "units"):
                raw_records = value.get(key)
                if isinstance(raw_records, list):
                    records.extend(
                        record
                        for record in raw_records
                        if isinstance(record, Mapping)
                    )

        reported: list[int] = []
        for key in (
            "completed_directions",
            "completed_sectors",
            "terminal_units",
        ):
            raw = value.get(key)
            if isinstance(raw, int) and not isinstance(raw, bool) and raw >= 0:
                reported.append(raw)
        attempted = max([len(records), *reported], default=0)

        xor_envelope = bool(
            source_kind == "xor"
            and value.get("schema_version") == 1
            and value.get("gate") == "qldpc-frontier-xor-sector-screen"
            and isinstance(candidate, Mapping)
            and required is not None
            and isinstance(value.get("sectors"), list)
            and value.get("completed_sectors") == len(value["sectors"])
        )
        direction_envelope = bool(
            source_kind == "directions"
            and value.get("schema_version") == 2
            and value.get("gate") == "qldpc-frontier-threshold-screen"
            and isinstance(candidate, Mapping)
            and required is not None
            and isinstance(value.get("threshold_only"), bool)
            and isinstance(value.get("directions"), list)
            and value.get("completed_directions") == len(value["directions"])
        )
        raw_candidate_k = (
            candidate.get("k") if isinstance(candidate, Mapping) else None
        )
        candidate_k = (
            raw_candidate_k
            if isinstance(raw_candidate_k, int)
            and not isinstance(raw_candidate_k, bool)
            and raw_candidate_k > 0
            else None
        )
        sat_expected = value.get("expected_units")
        sat_planned_expected: int | None = None
        if isinstance(candidate, Mapping):
            try:
                from scripts.audit_direction_pool import expected_proof_units

                sat_planned_expected = expected_proof_units(
                    candidate, "sat-sectors",
                )
            except (KeyError, TypeError, ValueError):
                # This is monitoring only.  A candidate that cannot be
                # reconstructed must not gain a trusted progress envelope.
                sat_planned_expected = None
        sat_isometry_valid = False
        stored_isometry = value.get("xz_sector_isometry")
        if (
            candidate_k is not None
            and isinstance(candidate, Mapping)
            and isinstance(stored_isometry, Mapping)
        ):
            try:
                import numpy as np

                from evaluation.bb_sector_isometry import (
                    verify_bb_xz_sector_isometry,
                )
                from scripts.screen_frontier_candidate import (
                    build_candidate_code,
                )

                rebuilt = build_candidate_code(dict(candidate))
                replayed_isometry = verify_bb_xz_sector_isometry(
                    np.asarray(rebuilt.matrix_x, dtype=np.uint8) & 1,
                    np.asarray(rebuilt.matrix_z, dtype=np.uint8) & 1,
                    ell=int(candidate["ell"]),
                    m=int(candidate["m"]),
                    geometry=candidate_geometry(candidate),
                )
                sat_isometry_valid = bool(
                    int(rebuilt.num_qudits) == candidate.get("n")
                    and int(rebuilt.dimension) == candidate_k
                    and replayed_isometry.get("verified") is True
                    and replayed_isometry.get("canonical_sector") == "X"
                    and replayed_isometry.get("covered_sectors") == ["X", "Z"]
                    and dict(stored_isometry) == replayed_isometry
                )
            except Exception:
                # Monitoring/progress accounting fails closed to the legacy
                # complete X/Z envelope.  It never promotes mathematical
                # evidence from an un-replayed report.
                sat_isometry_valid = False
        sat_expected_valid = bool(
            (
                sat_planned_expected is not None
                and sat_expected == sat_planned_expected
            )
            or sat_expected == 4
            or (
                candidate_k is not None
                and sat_expected == 2 * candidate_k + 2
            )
            or (
                sat_isometry_valid
                and candidate_k is not None
                and sat_expected in {2, candidate_k + 1}
            )
        )
        sat_sector_envelope = bool(
            source_kind == "sat-sectors"
            and value.get("schema_version") == 1
            and value.get("gate")
            == "qldpc-frontier-sat-sector-exact-screen"
            and isinstance(candidate, Mapping)
            and required is not None
            and isinstance(value.get("units"), list)
            and value.get("attempted_units") == len(value["units"])
            and sat_expected_valid
        )

        if sat_sector_envelope:
            terminal = timed_out = proven = 0
            for unit in records:
                evidence = unit.get("solver_evidence")
                if not isinstance(evidence, Mapping):
                    continue
                unsigned = dict(evidence)
                stored_sha256 = unsigned.pop("evidence_sha256", None)
                hash_valid = bool(
                    isinstance(stored_sha256, str)
                    and stored_sha256 == _canonical_sha256(unsigned)
                )
                outcome = evidence.get("outcome")
                complete = bool(
                    hash_valid
                    and evidence.get("decision_complete") is True
                    and outcome in {"sat", "unsat"}
                )
                terminal += complete
                timed_out += outcome == "hard_timeout"
                objective = evidence.get("objective")
                lower_proof = bool(
                    complete
                    and unit.get("phase") in {"lower", "lower-global"}
                    and outcome == "unsat"
                    and evidence.get("threshold_infeasible") is True
                    and evidence.get("max_weight") == required - 1
                )
                upper_witness = bool(
                    complete
                    and unit.get("phase") == "upper"
                    and outcome == "sat"
                    and isinstance(objective, int)
                    and not isinstance(objective, bool)
                    and objective == required
                )
                proven += lower_proof or upper_witness
            return {
                "attempted_units": len(records),
                "terminal_units": terminal,
                "timeout_units": timed_out,
                "proven_units": proven,
                "completed_units": terminal,
                "reported_completed_units": int(
                    value.get("terminal_units", 0) or 0
                ),
            }

        binding = value.get("binding")
        matrix_hashes = (
            binding.get("matrix_sha256")
            if isinstance(binding, Mapping)
            else None
        )
        legacy_checkpoint_envelope = bool(
            source_kind in {"checkpoints", "strict-verification"}
            and value.get("schema_version") == 1
            and value.get("checkpoint_type")
            in {
                "qldpc-css-bb-build-checkpoint-v1",
                "qldpc-css-bb-verify-checkpoint-v1",
            }
            and isinstance(binding, Mapping)
            and is_selection_sha256(binding.get("claim_sha256"))
            and is_selection_sha256(binding.get("known_answer_sha256"))
            and isinstance(matrix_hashes, Mapping)
            and set(matrix_hashes) == {"hx", "hz"}
            and all(
                is_selection_sha256(item)
                for item in matrix_hashes.values()
            )
            and isinstance(binding.get("solver"), Mapping)
            and isinstance(value.get("directions"), list)
            and value.get("completed_directions") == len(value["directions"])
        )

        proof_binding = value.get("proof_binding")
        proof_binding_valid = False
        if isinstance(proof_binding, Mapping):
            unsigned_proof_binding = dict(proof_binding)
            proof_binding_sha256 = unsigned_proof_binding.pop(
                "binding_sha256", None
            )
            proof_binding_valid = bool(
                isinstance(proof_binding_sha256, str)
                and proof_binding_sha256
                == _canonical_sha256(unsigned_proof_binding)
            )
        css_checkpoint_envelope = bool(
            source_kind in {"checkpoints", "strict-verification"}
            and value.get("kind") == "qcode-css-distance-milp-checkpoint"
            and value.get("schema_version") == 2
            and proof_binding_valid
            and isinstance(raw_direction_results, Mapping)
        )

        terminal = 0
        timed_out = 0
        proven = 0
        for record in records:
            status_values = [
                record.get("status"),
                record.get("status_name"),
                record.get("outcome"),
                record.get("last_attempt_status"),
                record.get("message"),
            ]
            status_text = " ".join(
                str(item).upper() for item in status_values if item is not None
            )
            backend_text = " ".join(
                str(record.get(key, "")).upper()
                for key in ("solver", "backend", "formulation")
            )
            is_timeout = any(
                marker in status_text
                for marker in (
                    "TIME LIMIT",
                    "TIME_LIMIT",
                    "TIMED OUT",
                    "TIMEOUT",
                    "HARD_TIMEOUT",
                    "NO_INCUMBENT",
                    "UNKNOWN",
                )
            )
            raw_status = record.get("status")
            if (
                raw_status == 1
                and any(name in backend_text for name in ("SCIPY", "HIGHS"))
            ):
                is_timeout = True
            if (
                raw_status == 0
                and "ORTOOLS" in backend_text
                and record.get("success") is not True
            ):
                is_timeout = True
            timed_out += is_timeout

            objective = record.get("objective", record.get("weight"))
            objective_is_int = (
                isinstance(objective, int) and not isinstance(objective, bool)
            )
            replay_verified_witness = bool(
                objective_is_int
                and record.get("witness_verified") is True
                and isinstance(record.get("operator"), Mapping)
            )
            correct_bound = bool(
                required is not None
                and record.get("max_weight") == required - 1
            )
            no_incumbent = bool(
                record.get("operator") is None
                and record.get("objective") is None
            )
            xor_threshold_proof = bool(
                xor_envelope
                and record.get("formulation") == "css-sector-xor-cpsat-v1"
                and record.get("solver") == "ortools-cp-sat"
                and record.get("status_name") == "INFEASIBLE"
                and record.get("threshold_infeasible") is True
                and correct_bound
                and no_incumbent
            )
            direction_threshold_proof = bool(
                direction_envelope
                and value.get("threshold_only") is True
                and record.get("formulation")
                == "css-logical-threshold-bounded-minimization-v2"
                and record.get("solver") == "scipy.optimize.milp"
                and record.get("backend") == "HiGHS"
                and record.get("status") == 2
                and record.get("success") is False
                and record.get("threshold_infeasible") is True
                and correct_bound
                and no_incumbent
            )
            artifact_exact_optimum = bool(
                replay_verified_witness
                and (
                    (
                        xor_envelope
                        and value.get("threshold_only") is False
                        and record.get("exact") is True
                        and record.get("status_name") == "OPTIMAL"
                    )
                    or (
                        direction_envelope
                        and value.get("threshold_only") is False
                        and record.get("formulation")
                        == "css-logical-anticommutation-milp-v1"
                        and record.get("solver") == "scipy.optimize.milp"
                        and record.get("backend") == "HiGHS"
                        and record.get("status") == 0
                        and record.get("success") is True
                        and record.get("mip_gap") == 0.0
                    )
                )
            )
            legacy_checkpoint_optimum = bool(
                legacy_checkpoint_envelope
                and objective_is_int
                and record.get("formulation")
                == "css-logical-anticommutation-milp-v1"
                and record.get("solver") == "scipy.optimize.milp"
                and record.get("backend") == "HiGHS"
                and record.get("status") == 0
                and record.get("success") is True
                and record.get("mip_gap") == 0.0
                and isinstance(record.get("mip_dual_bound"), (int, float))
                and not isinstance(record.get("mip_dual_bound"), bool)
                and math.isfinite(float(record["mip_dual_bound"]))
                and math.isclose(
                    float(record["mip_dual_bound"]),
                    float(objective),
                    rel_tol=0.0,
                    abs_tol=1e-7,
                )
                and isinstance(record.get("operator"), Mapping)
                and isinstance(record.get("target_logical"), Mapping)
            )
            css_checkpoint_optimum = bool(
                css_checkpoint_envelope
                and str(record.get("status", "")).lower() == "optimal"
                and record.get("optimal") is True
                and objective_is_int
                and isinstance(record.get("witness"), Mapping)
            )
            is_proven = bool(
                xor_threshold_proof
                or direction_threshold_proof
                or artifact_exact_optimum
                or legacy_checkpoint_optimum
                or css_checkpoint_optimum
            )
            rejected_witness = bool(
                (xor_envelope or direction_envelope)
                and replay_verified_witness
                and required is not None
                and int(objective) < required
            )
            is_terminal = is_proven or rejected_witness
            proven += is_proven
            terminal += is_terminal

        return {
            "attempted_units": attempted,
            "terminal_units": terminal,
            "timeout_units": timed_out,
            "proven_units": proven,
            # Backward-compatible field with corrected semantics.  A timeout
            # is attempted work, never a completed proof unit.
            "completed_units": terminal,
            "reported_completed_units": max(reported, default=0),
        }

    def _strict_progress_tokens(
        self,
        selected_digests: set[str],
    ) -> set[str]:
        """Map selected candidates to Stage 5 certificate-payload filenames."""

        tokens: set[str] = set()
        if not self.paths.stage4_certificates.is_file():
            return tokens
        try:
            lines = self.paths.stage4_certificates.read_text().splitlines()
        except (OSError, UnicodeError):
            return tokens
        for line in lines:
            if not line.strip():
                continue
            try:
                certificate = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(certificate, Mapping):
                continue
            claim = certificate.get("claim")
            digest = (
                claim.get("canonical_digest")
                if isinstance(claim, Mapping)
                else None
            )
            if digest in selected_digests:
                tokens.add(_canonical_sha256(certificate))
        return tokens

    def _proof_progress_snapshot(
        self,
        *,
        selected_digests: Iterable[str] | None = None,
    ) -> dict[str, Any]:
        """Classify durable proof units bound to the active candidate page."""

        self._ensure_solver_state_tree_safe()
        if selected_digests is None:
            binding = self._current_proof_retry_binding()
            selected_digests = (
                binding.get("selected_digests", [])
                if isinstance(binding, Mapping)
                else []
            )
        selected = {
            digest
            for digest in selected_digests
            if isinstance(digest, str) and digest
        }
        path_tokens = {
            digest for digest in selected
        } | {
            hashlib.sha256(digest.encode()).hexdigest() for digest in selected
        }
        strict_tokens = self._strict_progress_tokens(selected)
        roots = (
            self.paths.solver_state / "xor",
            self.paths.solver_state / "directions",
            self.paths.solver_state / "sat-sectors",
            self.paths.solver_state / "twobga-aux",
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
                digest = self._proof_checkpoint_candidate_digest(value)
                token = path.name.split(".", 1)[0]
                allowed_tokens = (
                    strict_tokens
                    if root.name == "strict-verification"
                    else path_tokens
                )
                if digest is not None:
                    if digest not in selected:
                        continue
                    # Candidate-bound content is authoritative, but its path
                    # must also belong to this page whenever the producer has
                    # a deterministic digest filename.
                    if root.name != "strict-verification" and token not in path_tokens:
                        continue
                elif token not in allowed_tokens:
                    continue
                counts = self._proof_checkpoint_record_counts(
                    value,
                    source_kind=root.name,
                )
                if not counts["attempted_units"]:
                    continue
                relative = path.relative_to(self.paths.solver_state).as_posix()
                units[relative] = {
                    **counts,
                    "candidate_digest": digest,
                    "sha256": _file_sha256(path),
                }
        aggregate_keys = (
            "attempted_units",
            "terminal_units",
            "timeout_units",
            "proven_units",
            "completed_units",
            "reported_completed_units",
        )
        return {
            key: sum(int(item[key]) for item in units.values())
            for key in aggregate_keys
        } | {
            "selected_digests": sorted(selected),
            "selected_digests_sha256": _canonical_sha256(sorted(selected)),
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
        """Return whether a bound unit became terminal or mathematically proven."""

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
            for key in ("terminal_units", "proven_units"):
                previous = (
                    raw_before.get(key, 0)
                    if isinstance(raw_before, Mapping)
                    else 0
                )
                current = raw_after.get(key, 0)
                if (
                    isinstance(previous, int)
                    and not isinstance(previous, bool)
                    and isinstance(current, int)
                    and not isinstance(current, bool)
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
        selected_digests = list(
            active.get("binding", {}).get("selected_digests", [])
        )
        progress = self._proof_progress_snapshot(
            selected_digests=selected_digests,
        )
        empty_progress = {
            "attempted_units": 0,
            "terminal_units": 0,
            "timeout_units": 0,
            "proven_units": 0,
            "completed_units": 0,
            "reported_completed_units": 0,
            "selected_digests": sorted(selected_digests),
            "selected_digests_sha256": _canonical_sha256(
                sorted(selected_digests)
            ),
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
        latest = attempts[-1]
        if not isinstance(latest, Mapping):
            return None, "INVALID_ATTEMPT_HISTORY"
        # PREPARE is the durable scheduling transaction.  Once an attempt is
        # persisted, a crash before execution must replay that exact budget;
        # neither the completed-attempt cap nor elapsed time may silently
        # cancel and defer it.
        if latest.get("status") == "PREPARED":
            multiplier = latest.get("multiplier")
            if isinstance(multiplier, (int, float)) and not isinstance(
                multiplier, bool
            ) and 1 <= float(multiplier) <= float(
                self.config.proof_retry_max_multiplier
            ):
                return float(multiplier), None
            return None, "INVALID_PREPARED_BUDGET"
        elapsed = active.get("elapsed_seconds", 0)
        if (
            not isinstance(elapsed, (int, float))
            or isinstance(elapsed, bool)
            or elapsed >= self.config.proof_retry_campaign_total_timeout
        ):
            return None, "CAMPAIGN_TOTAL_TIMEOUT_REACHED"
        multiplier = float(latest.get("multiplier", 1))
        # A monotone, checkpoint-verified gain renews the attempt lease at the
        # same budget.  This remains bounded by the campaign wall above; the
        # count cap is reserved for completed attempts that made no progress.
        if latest.get("made_progress") is True:
            return multiplier, None
        if len(attempts) >= self.config.proof_retry_max_attempts:
            return None, "MAX_ATTEMPTS_REACHED"
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
                "progress_before": self._proof_progress_snapshot(
                    selected_digests=active.get("binding", {}).get(
                        "selected_digests", []
                    ),
                ),
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
        after = self._proof_progress_snapshot(
            selected_digests=active.get("binding", {}).get(
                "selected_digests", []
            ),
        )
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

    def _proof_scheduler_signature(
        self,
        controller: Mapping[str, Any],
    ) -> str:
        """Hash only monotone scheduler state used to justify another pass."""

        ledger_state: dict[str, Any] | None = None
        if self.paths.stage2_selection_ledger.is_file():
            ledger = self._validated_stage2_selection_ledger(
                _read_json_object(self.paths.stage2_selection_ledger)
            )
            ledger_state = {
                "binding_sha256": ledger.get("binding_sha256"),
                "snapshot_identity_sha256": ledger.get(
                    "snapshot_identity_sha256"
                ),
                "cursor": ledger.get("cursor"),
                "committed_digests": ledger.get("committed_digests"),
                "pending": ledger.get("pending"),
                "last_ack_sha256": ledger.get("last_ack_sha256"),
                "progress_sha256": ledger.get("progress_sha256"),
                "deferred_page_hashes": [
                    entry.get("entry_sha256")
                    for entry in ledger.get("deferred_pages", [])
                    if isinstance(entry, Mapping)
                ]
                if isinstance(ledger.get("deferred_pages", []), list)
                else None,
            }
        active = controller.get("active")
        active_state: dict[str, Any] | None = None
        if isinstance(active, Mapping):
            attempts = active.get("attempts")
            active_state = {
                "binding_sha256": active.get("binding_sha256"),
                "status": active.get("status"),
                "cap_reason": active.get("cap_reason"),
                "attempts": [
                    {
                        "attempt": attempt.get("attempt"),
                        "multiplier": attempt.get("multiplier"),
                        "status": attempt.get("status"),
                        "made_progress": attempt.get("made_progress"),
                    }
                    for attempt in attempts
                    if isinstance(attempt, Mapping)
                ]
                if isinstance(attempts, list)
                else None,
            }
        return _canonical_sha256(
            {"selection_ledger": ledger_state, "retry_active": active_state}
        )

    def _rotate_deferred_generation_for_budget_change(self) -> bool:
        """Start a fresh finite scan when any deferred dependency changes.

        Automatic retry multipliers never alter ``_proof_retry_base_config``;
        an explicit budget change does.  Search identity/output, proof and
        strict sources, registry, runtime, or trusted inputs changing must
        rotate too: otherwise the terminal-restore shortcut could return an
        old INCOMPLETE result before normal stage-cache invalidation runs.
        The old ledger is archived before the one atomic live-ledger replace.
        """

        if not self.paths.stage2_selection_ledger.is_file():
            return False
        self._ensure_solver_state_tree_safe()
        ledger = _read_json_object(self.paths.stage2_selection_ledger)
        if (
            ledger.get("schema_version")
            != STAGE2_SELECTION_LEDGER_SCHEMA_VERSION
            or ledger.get("gate") != STAGE2_SELECTION_LEDGER_GATE
        ):
            # The Stage 2 CLI owns migration. Its changed source fingerprint
            # forces a rerun, where the stale schema is reset at cursor zero.
            return False
        deferred_pages = self._validate_deferred_stage2_pages(ledger)
        if not deferred_pages:
            return False

        current_environment = self._proof_retry_environment_binding()
        current_environment_sha256 = _canonical_sha256(current_environment)
        deferred_proof_configs: set[str] = set()
        deferred_environments: set[str] = set()
        for entry in deferred_pages:
            manifest_path = (
                self.paths.solver_state / str(entry["manifest_path"])
            )
            manifest = _read_json_object(manifest_path)
            active = manifest.get("proof_retry_active")
            binding = (
                active.get("binding")
                if isinstance(active, Mapping)
                else None
            )
            proof_config_sha256 = (
                binding.get("proof_config_sha256")
                if isinstance(binding, Mapping)
                else None
            )
            if not isinstance(proof_config_sha256, str):
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "deferred page lacks its base proof configuration",
                    stage="stage2_sector_audit",
                )
            deferred_proof_configs.add(proof_config_sha256)
            # Page-local fields intentionally differ.  Compare the complete
            # dependency subset required to justify skipping all live stages.
            # A legacy binding that lacks a newly required field maps it to
            # None and therefore rotates fail-closed.
            deferred_environments.add(
                _canonical_sha256(
                    {
                        field: (
                            binding.get(field)
                            if isinstance(binding, Mapping)
                            else None
                        )
                        for field in current_environment
                    }
                )
            )
        if len(deferred_proof_configs) != 1:
            raise PipelineError(
                "OUTPUT_INVALID",
                "one Stage 2 generation mixes base proof configurations",
                stage="stage2_sector_audit",
            )
        previous_proof_config_sha256 = next(
            iter(deferred_proof_configs)
        )
        current_proof_config_sha256 = _canonical_sha256(
            self._proof_retry_base_config()
        )
        proof_config_changed = (
            previous_proof_config_sha256
            != current_proof_config_sha256
        )
        environment_changed = deferred_environments != {
            current_environment_sha256
        }
        if not proof_config_changed and not environment_changed:
            return False

        generation = ledger.get("generation", 0)
        history = ledger.get("generation_history", [])
        if (
            isinstance(generation, bool)
            or not isinstance(generation, int)
            or generation < 0
            or not isinstance(history, list)
            or any(not isinstance(item, Mapping) for item in history)
        ):
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 ledger generation metadata is malformed",
                stage="stage2_sector_audit",
            )
        old_ledger_bytes = _read_regular_nofollow(
            self.paths.stage2_selection_ledger
        )
        old_ledger_sha256 = hashlib.sha256(old_ledger_bytes).hexdigest()
        archive_relative = (
            Path("selection-ledger-generations")
            / (
                f"generation-{generation:06d}-"
                f"{old_ledger_sha256[:16]}.json"
            )
        )
        archive_path = _reject_symlink_components(
            self.paths.solver_state / archive_relative,
            classification="UNSAFE_CONTROL_PATH",
            label="Stage 2 ledger generation archive",
        )
        archive_path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        if archive_path.is_file():
            if _read_regular_nofollow(archive_path) != old_ledger_bytes:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "existing Stage 2 ledger generation archive differs",
                    stage="stage2_sector_audit",
                )
        else:
            try:
                archive_text = old_ledger_bytes.decode("utf-8")
            except UnicodeDecodeError as exc:
                raise PipelineError(
                    "OUTPUT_INVALID",
                    "Stage 2 selection ledger is not UTF-8 JSON",
                    stage="stage2_sector_audit",
                ) from exc
            _atomic_write_text(archive_path, archive_text)
        if _file_sha256(archive_path) != old_ledger_sha256:
            raise PipelineError(
                "OUTPUT_INVALID",
                "Stage 2 ledger generation archive hash does not replay",
                stage="stage2_sector_audit",
            )

        history_payload = {
            "schema_version": 1,
            "gate": STAGE2_LEDGER_GENERATION_GATE,
            "generation": generation,
            "binding_sha256": ledger.get("binding_sha256"),
            "proof_config_sha256": previous_proof_config_sha256,
            "environment_binding_sha256": sorted(
                deferred_environments
            ),
            "replacement_environment_binding_sha256": (
                current_environment_sha256
            ),
            "rotation_reasons": [
                reason
                for reason, changed in (
                    ("PROOF_CONFIG_CHANGED", proof_config_changed),
                    ("DEPENDENCY_BINDING_CHANGED", environment_changed),
                )
                if changed
            ],
            "ledger_path": archive_relative.as_posix(),
            "ledger_sha256": old_ledger_sha256,
            "deferred_pages": len(deferred_pages),
            "deferred_candidates": sum(
                len(entry["selected_digests"])
                for entry in deferred_pages
            ),
            "archived_at": utc_now(),
        }
        history_entry = {
            **history_payload,
            "entry_sha256": _canonical_sha256(history_payload),
        }
        reset_ledger = new_selection_ledger(
            binding_sha256=ledger["binding_sha256"],
            snapshot_identity_sha256_value=ledger[
                "snapshot_identity_sha256"
            ],
            snapshot_rows=ledger["snapshot_rows"],
            eligible_rows=ledger["eligible_rows"],
            generation=generation + 1,
            proof_config_sha256=current_proof_config_sha256,
            generation_history=[*history, history_entry],
        )
        # Generation archive is durable before this single transaction point.
        atomic_write_json(
            self.paths.stage2_selection_ledger, reset_ledger
        )
        self._ensure_solver_state_tree_safe()
        pagination = self.state.setdefault("stage2_pagination", {})
        pagination.update(
            {
                "generation": generation + 1,
                "cursor": 0,
                "completed_pages": 0,
                "deferred_pages": 0,
                "selection_exhausted": False,
                "proof_config_sha256": current_proof_config_sha256,
                "previous_proof_config_sha256": (
                    previous_proof_config_sha256
                ),
                "environment_binding_sha256": (
                    current_environment_sha256
                ),
                "previous_environment_binding_sha256": sorted(
                    deferred_environments
                ),
                "generation_rotated_at": utc_now(),
                "generation_archive": archive_relative.as_posix(),
            }
        )
        self._write_state()
        return True

    def _restore_completed_deferred_scan(self) -> bool:
        """Recover a crash after the terminal cursor commit, before state."""

        if (
            self.state.get("status") != "INCOMPLETE"
            or not self.paths.stage2_selection_ledger.is_file()
        ):
            return False
        ledger = _read_json_object(self.paths.stage2_selection_ledger)
        if (
            ledger.get("schema_version")
            != STAGE2_SELECTION_LEDGER_SCHEMA_VERSION
            or ledger.get("gate") != STAGE2_SELECTION_LEDGER_GATE
        ):
            return False
        pages = self._validate_deferred_stage2_pages(ledger)
        if not pages or ledger.get("pending") is not None:
            return False
        pagination = self.state.get("stage2_pagination")
        state_says_exhausted = bool(
            isinstance(pagination, Mapping)
            and pagination.get("selection_exhausted") is True
            and pagination.get("cursor") == ledger.get("cursor")
        )
        last_page_sha256 = ledger.get("last_acknowledged_page_sha256")
        artifact_says_exhausted = False
        if self.paths.stage2_summary.is_file():
            summary = _read_json_object(self.paths.stage2_summary)
            page = summary.get("selection_page")
            artifact_says_exhausted = bool(
                isinstance(page, Mapping)
                and page.get("page_sha256") == last_page_sha256
                and summary.get("selection_exhausted") is True
            )
        deferred_terminal = bool(
            pages[-1].get("page_sha256") == last_page_sha256
            and pages[-1].get("selection_exhausted") is True
        )
        if not (
            state_says_exhausted
            or artifact_says_exhausted
            or deferred_terminal
        ):
            return False

        result = self.state.get("result")
        if not isinstance(result, dict):
            raise PipelineError(
                "OUTPUT_INVALID",
                "terminal deferred scan lacks its fail-closed result",
                stage="stage2_sector_audit",
            )
        incompleteness = result.get("proof_incompleteness")
        if not isinstance(incompleteness, Mapping):
            raise PipelineError(
                "OUTPUT_INVALID",
                "terminal deferred scan lacks proof incompleteness",
                stage="stage2_sector_audit",
            )
        result["proof_incompleteness"] = (
            self._carry_deferred_stage2_incompleteness(incompleteness)
        )
        repaired = self.state.setdefault("stage2_pagination", {})
        repaired.update(
            {
                "binding_sha256": ledger.get("binding_sha256"),
                "cursor": ledger.get("cursor"),
                "completed_pages": ledger.get("completed_pages"),
                "deferred_pages": len(pages),
                "selection_exhausted": True,
                "last_page_sha256": last_page_sha256,
                "recovered_terminal_commit_at": utc_now(),
            }
        )
        self._write_state()
        return True

    def _run_locked(self) -> dict[str, Any]:
        # One proof pass may bind one feedback-derived Stage 1 identity. Drop
        # leases from the previous completed pass before selecting/replaying
        # the next identity; the base campaign lease remains held throughout.
        self._reset_derived_humanize_run_leases()
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
            # Capture once. audit_candidate_pool.py owns this transaction and
            # may advance pending/cursor while the machine is running.
            stage2_selection_ledger_prestate_sha256 = (
                self._stage2_selection_ledger_prestate_sha256()
            )
            stage2_static_config = {
                "top": self.config.stage2_top,
                "timeout": self._scaled_proof_timeout(
                    self.config.stage2_timeout
                ),
                "proof_budget_multiplier": self._proof_budget_multiplier,
                "candidate_workers": self.config.stage2_candidate_workers,
                "solver_workers": self.config.stage2_solver_workers,
                "compact_low_weight_max_weight": (
                    self.config.stage2_compact_low_weight_max_weight
                ),
                "structural_workers": self.config.max_total_workers,
                "structural_hard_timeout": self._scaled_proof_timeout(
                    self.config.stage2_timeout
                ),
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
                "resume": self.config.resume or self._proof_retry_resume,
                "selection_ledger_prestate_sha256": (
                    stage2_selection_ledger_prestate_sha256
                ),
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
                validator=lambda: self._validate_stage2_selection_lifecycle(
                    self._validate_pool_summary(
                        self.paths.stage2_summary,
                        self.paths.stage2_ranked,
                        "qldpc-proof-oriented-candidate-pool",
                    ),
                ),
                recoverable_exit_codes=RECOVERABLE_PROOF_EXIT_CODES,
                nonzero_validator=lambda: (
                    self._validate_stage2_selection_lifecycle(
                        self._validate_recoverable_pool_summary(
                            self.paths.stage2_summary,
                            self.paths.stage2_ranked,
                            "qldpc-proof-oriented-candidate-pool",
                        ),
                    )
                ),
            )
            if self._flow_config().evolution_evaluator == "coset-two-block":
                self._archive_stage2_coset_negatives(candidates)

            has_unresolved = any(
                isinstance(result, Mapping)
                and result.get("status") == "UNRESOLVED"
                and result.get("retry_required") is not True
                for result in stage2.get("results", [])
            )
            if has_unresolved:
                stage3_command = self._stage3_command()
                stage3_inputs = [
                    self.paths.stage2_ranked,
                    self.config.repo_dir / "scripts" / "audit_direction_pool.py",
                    self.config.repo_dir
                    / "scripts"
                    / {
                        "legacy-directions": "screen_frontier_candidate.py",
                        "sat-sectors": "screen_frontier_sat.py",
                        "twobga-aux": "screen_frontier_twobga.py",
                    }[self.config.stage3_backend],
                    *(
                        [
                            self.config.repo_dir
                            / "evaluation"
                            / "twobga_subsystem.py",
                        ]
                        if self.config.stage3_backend == "twobga-aux"
                        else []
                    ),
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
                "backend": self.config.stage3_backend,
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
                "resume": self.config.resume or self._proof_retry_resume,
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
            if self._flow_config().evolution_evaluator == "coset-two-block":
                self._archive_stage3_coset_negatives(candidates, stage3)

            proof_incompleteness = self._proof_incompleteness(stage2, stage3)
            proof_incompleteness = self._carry_paginated_input_incompleteness(
                stage2,
                proof_incompleteness,
            )
            proof_incompleteness = (
                self._carry_deferred_stage2_incompleteness(
                    proof_incompleteness
                )
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
                    "verification_sidecar_schema": (
                        CERTIFICATE_CACHE_SCHEMA_VERSION
                    ),
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
                effective_resume = bool(
                    self.config.resume or self._proof_retry_resume
                )
                strict_command = self._strict_command(
                    effective_resume=effective_resume,
                )
                stage5_static_config = {
                    "mode": "strict",
                    # This is deliberately distinct from config.resume.  A
                    # fresh campaign may start with resume=False, while the
                    # durable proof-retry controller must resume validated
                    # checkpoints on its later attempts.  Bind the effective
                    # value that was actually passed to the strict runner.
                    "effective_resume": effective_resume,
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
                        *self._strict_verifier_sources(),
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
            self._load_or_initialize_state()
            try:
                self._rotate_deferred_generation_for_budget_change()
                if self._restore_completed_deferred_scan():
                    return self.state
            except PipelineError as exc:
                return self._record_failure(exc)
            # max_attempts=1 is the explicit compatibility/diagnostic mode:
            # one proof pass per invocation and no in-process retry sleep.
            if self.config.proof_retry_max_attempts == 1:
                state: dict[str, Any] = {}
                automatic_pass = 0
                while True:
                    automatic_pass += 1
                    state = self._run_locked()
                    if state.get("status") != "INCOMPLETE":
                        return state
                    try:
                        advanced = self._acknowledge_completed_stage2_page(
                            state
                        )
                    except PipelineError as exc:
                        return self._record_failure(exc)
                    if advanced:
                        summary = _read_json_object(self.paths.stage2_summary)
                        selection_exhausted = summary.get(
                            "selection_exhausted"
                        )
                        if not isinstance(selection_exhausted, bool):
                            return self._record_failure(
                                PipelineError(
                                    "OUTPUT_INVALID",
                                    "Stage 2 page lacks selection exhaustion status",
                                    stage="stage2_sector_audit",
                                )
                            )
                        self.state.setdefault("stage2_pagination", {})[
                            "automatic_passes"
                        ] = automatic_pass
                        self._write_state()
                        if selection_exhausted:
                            return state
                        continue
                    return state

            # Load once before selecting a recovered PREPARED retry.  Each
            # _run_locked call reloads again before executing its stage state
            # machine, so a killed process can resume the same prepared budget.
            self._load_or_initialize_state()
            controller = self._load_proof_retry_controller()
            force_fresh_page = False
            state: dict[str, Any] = {}
            automatic_pass = 0
            while True:
                automatic_pass += 1
                scheduler_before = self._proof_scheduler_signature(controller)
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
                        reason = str(
                            active.get(
                                "cap_reason",
                                "RETRY_CONTROLLER_ALREADY_CAPPED",
                            )
                        )
                        try:
                            deferred, has_later_page = (
                                self._defer_capped_stage2_page(
                                    controller,
                                    active,
                                    reason,
                                )
                            )
                        except PipelineError as exc:
                            return self._record_failure(exc)
                        if not deferred:
                            return self._mark_proof_retry_capped(
                                controller, active, reason
                            )
                        force_fresh_page = True
                        self.state.setdefault("stage2_pagination", {})[
                            "automatic_passes"
                        ] = automatic_pass
                        self._write_state()
                        if not has_later_page:
                            return self.state
                        if (
                            self._proof_scheduler_signature(controller)
                            == scheduler_before
                        ):
                            return self._record_failure(
                                PipelineError(
                                    "NO_PROOF_SCHEDULER_PROGRESS",
                                    "deferred proof page did not move scheduler state",
                                    stage="stage2_sector_audit",
                                )
                            )
                        continue
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
                            reason = (
                                cap_reason or "RETRY_BUDGET_EXHAUSTED"
                            )
                            try:
                                deferred, has_later_page = (
                                    self._defer_capped_stage2_page(
                                        controller,
                                        active,
                                        reason,
                                    )
                                )
                            except PipelineError as exc:
                                return self._record_failure(exc)
                            if not deferred:
                                return self._mark_proof_retry_capped(
                                    controller, active, reason
                                )
                            force_fresh_page = True
                            self.state.setdefault(
                                "stage2_pagination", {}
                            )["automatic_passes"] = automatic_pass
                            self._write_state()
                            if not has_later_page:
                                return self.state
                            if (
                                self._proof_scheduler_signature(controller)
                                == scheduler_before
                            ):
                                return self._record_failure(
                                    PipelineError(
                                        "NO_PROOF_SCHEDULER_PROGRESS",
                                        "capped proof page did not advance its cursor",
                                        stage="stage2_sector_audit",
                                    )
                                )
                            continue
                        prepared = self._prepare_proof_retry_attempt(
                            controller,
                            active,
                            multiplier,
                        )

                self._proof_budget_multiplier = multiplier
                self._proof_retry_resume = prepared is not None
                started = self._monotonic()
                try:
                    state = self._run_locked()
                finally:
                    duration = max(0.0, self._monotonic() - started)
                    self._proof_budget_multiplier = 1.0
                    self._proof_retry_resume = False

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
                    summary = _read_json_object(self.paths.stage2_summary)
                    selection_exhausted = summary.get(
                        "selection_exhausted"
                    )
                    if not isinstance(selection_exhausted, bool):
                        return self._record_failure(
                            PipelineError(
                                "OUTPUT_INVALID",
                                "Stage 2 page lacks selection exhaustion status",
                                stage="stage2_sector_audit",
                            )
                        )
                    if selection_exhausted:
                        return state
                    if (
                        self._proof_scheduler_signature(controller)
                        == scheduler_before
                    ):
                        return self._record_failure(
                            PipelineError(
                                "NO_PROOF_SCHEDULER_PROGRESS",
                                "Stage 2 cursor acknowledgement made no progress",
                                stage="stage2_sector_audit",
                            )
                        )
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
                    reason = cap_reason or "RETRY_BUDGET_EXHAUSTED"
                    try:
                        deferred, has_later_page = (
                            self._defer_capped_stage2_page(
                                controller,
                                active,
                                reason,
                            )
                        )
                    except PipelineError as exc:
                        return self._record_failure(exc)
                    if not deferred:
                        return self._mark_proof_retry_capped(
                            controller, active, reason
                        )
                    force_fresh_page = True
                    self.state.setdefault("stage2_pagination", {})[
                        "automatic_passes"
                    ] = automatic_pass
                    self._write_state()
                    if not has_later_page:
                        return self.state
                    if (
                        self._proof_scheduler_signature(controller)
                        == scheduler_before
                    ):
                        return self._record_failure(
                            PipelineError(
                                "NO_PROOF_SCHEDULER_PROGRESS",
                                "proof deferral made no scheduler progress",
                                stage="stage2_sector_audit",
                            )
                        )
                    continue
                self.state.setdefault("stage2_pagination", {})[
                    "automatic_passes"
                ] = automatic_pass
                self._write_state()
                if (
                    self._proof_scheduler_signature(controller)
                    == scheduler_before
                ):
                    return self._record_failure(
                        PipelineError(
                            "NO_PROOF_SCHEDULER_PROGRESS",
                            "proof retry controller scheduled no new bounded work",
                            stage="stage2_sector_audit",
                        )
                    )


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
