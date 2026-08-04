"""Export an immutable release snapshot from a completed five-stage run.

The exporter deliberately does not rerun any solver.  It converts the exact
Stage 4 certificates and the independently replayed Stage 5 results into the
legacy release layout consumed by ``verify_release.py``.  Every relationship
between those artifacts is checked while holding the source pipeline lock.
"""

from __future__ import annotations

import ctypes
import errno
import fcntl
import hashlib
import importlib.util
import json
import marshal
import math
import os
import re
import stat
import sys
import tempfile
import types
from collections.abc import Iterable, Mapping
from contextlib import contextmanager
from pathlib import Path
from typing import Any

from evaluation.bb_code import build_bb_code
from evaluation.bb_sector_isometry import verify_bb_xz_sector_isometry
from evaluation.distance_milp import get_code_matrices
from evaluation.failure_disposition import (
    CERTIFICATE_CACHE_SCHEMA_VERSION,
    EVIDENCE_CONTRADICTION,
    INCOMPLETE as FAILURE_INCOMPLETE,
    validate_failure_disposition,
)
from evaluation.final_gate import classify_win
from evaluation.geometry import candidate_geometry
from evaluation.proof_runtime import (
    RuntimeProbeError,
    known_answer_environment,
    probe_python_runtime,
    resolve_python_executable,
    validate_proof_runtime_fingerprint,
)
from evaluation.release_gate import canonical_sha256, validate_release_manifest

_RUN_ID_PATTERN = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
_LOWER_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
_SUPPORTED_CERTIFICATE_TYPES = {
    "qldpc-css-bb-exact",
    "qldpc-css-matrix-exact",
    "qldpc-pbb-noncss-exact",
    "qldpc-noncss-matrix-exact",
    "qldpc-css-bb-sector-sat-exact",
    "qldpc-css-bb-twobga-subsystem-exact",
}
_SECTOR_SAT_CERTIFICATE_TYPE = "qldpc-css-bb-sector-sat-exact"
_TWOBGA_CERTIFICATE_TYPE = "qldpc-css-bb-twobga-subsystem-exact"
_TWOBGA_FORMULATION = "css-bb-exact-via-dressed-twobga-subsystem-v1"
_TWOBGA_EXACT_PROOF_TYPE = "qldpc-css-twobga-subsystem-exact-proof-v1"
_STAGE4 = "stage4_certificate_merge"
_STAGE5 = "stage5_strict_gate"
_STRICT_VERIFIER_SCRIPT_NAMES = (
    "screen_frontier_candidate.py",
    "screen_frontier_sat.py",
    "screen_frontier_xor.py",
    "screen_frontier_twobga.py",
)
_STAGE_ORDER = (
    "stage1_search",
    "stage2_sector_audit",
    "stage3_direction_audit",
    _STAGE4,
    _STAGE5,
)
_REQUIRED_REPLAY_CHECKS = frozenset(
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
_SECTOR_SAT_REQUIRED_REPLAY_CHECKS = frozenset(
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
_TWOBGA_REQUIRED_REPLAY_CHECKS = frozenset(
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
_UNTRUSTED_IMPORT_ARTIFACT_SUFFIXES = (
    ".so",
    ".pyd",
    ".dll",
    ".dylib",
    ".pyc",
    ".pyo",
)


def _strict_replay_contract(
    certificate: Mapping[str, Any],
    result: Mapping[str, Any],
    *,
    k: int,
) -> tuple[frozenset[str], bool]:
    """Return the typed replay-check set and its non-fictitious work count."""

    if certificate.get("certificate_type") == _TWOBGA_CERTIFICATE_TYPE:
        checks = result.get("checks")
        rerun = result.get("rerun")
        completed = (
            rerun.get("completed_sectors")
            if isinstance(rerun, Mapping)
            else None
        )
        expected = (
            rerun.get("expected_sectors")
            if isinstance(rerun, Mapping)
            else None
        )
        rerun_results = (
            rerun.get("results") if isinstance(rerun, Mapping) else None
        )
        sectors = (
            [item.get("sector") for item in rerun_results]
            if isinstance(rerun_results, list)
            and all(isinstance(item, Mapping) for item in rerun_results)
            else None
        )
        valid = bool(
            isinstance(checks, Mapping)
            and checks.get("theorem_eligibility") is True
            and checks.get("typed_exact_proof") is True
            and checks.get("independent_auxiliary_rerun") is True
            and isinstance(rerun, Mapping)
            and rerun.get("requested") is True
            and rerun.get("matches") is True
            and rerun.get("cardinality_encoding") == "seqcounter"
            and rerun.get("solver") == "glucose42"
            and isinstance(completed, int)
            and not isinstance(completed, bool)
            and isinstance(expected, int)
            and not isinstance(expected, bool)
            and completed == expected == 2
            and sectors == ["X", "Z"]
            and all(
                isinstance(item.get("solver_evidence"), Mapping)
                for item in rerun_results
            )
            and "directions_verified" not in result
            and "directions_total" not in result
            and "sector_decisions_verified" not in result
            and "sector_decisions_total" not in result
            and "logical_partitions_verified" not in result
            and "logical_partitions_total" not in result
            and "milp" not in certificate
            and "sector_exact" not in certificate
        )
        return _TWOBGA_REQUIRED_REPLAY_CHECKS, valid
    if certificate.get("certificate_type") == _SECTOR_SAT_CERTIFICATE_TYPE:
        expected = _sector_sat_expected_lower_decisions(certificate)
        claim = certificate.get("claim")
        proof = (
            claim.get("exact_distance_proof")
            if isinstance(claim, Mapping)
            else {}
        )
        expected_partitions = (
            proof.get("expected_lower_partitions")
            if isinstance(proof, Mapping)
            else None
        )
        if expected_partitions is None:
            sector_exact = certificate.get("sector_exact")
            expected_partitions = (
                sector_exact.get("expected_lower_partitions")
                if isinstance(sector_exact, Mapping)
                else None
            )
        if expected_partitions is None:
            # Legacy single-anchor certificates did not store the diagnostic
            # partition count.  The decision count equals the logical count.
            expected_partitions = expected
        verified = result.get("sector_decisions_verified")
        total = result.get("sector_decisions_total")
        partitions_verified = result.get("logical_partitions_verified")
        partitions_total = result.get("logical_partitions_total")
        checks = result.get("checks")
        valid = bool(
            isinstance(checks, Mapping)
            and checks.get("xz_sector_isometry") is True
            and checks.get("anchor_cover_cubes") is True
            and isinstance(verified, int)
            and not isinstance(verified, bool)
            and isinstance(total, int)
            and not isinstance(total, bool)
            and verified == total == expected
            and isinstance(partitions_verified, int)
            and not isinstance(partitions_verified, bool)
            and isinstance(partitions_total, int)
            and not isinstance(partitions_total, bool)
            and partitions_verified
            == partitions_total
            == expected_partitions
            and "directions_verified" not in result
            and "directions_total" not in result
            and "milp" not in certificate
        )
        return _SECTOR_SAT_REQUIRED_REPLAY_CHECKS, valid
    directions_verified = result.get("directions_verified")
    directions_total = result.get("directions_total")
    valid = bool(
        isinstance(directions_verified, int)
        and not isinstance(directions_verified, bool)
        and isinstance(directions_total, int)
        and not isinstance(directions_total, bool)
        and directions_verified == 2 * k
        and directions_total == 2 * k
    )
    return _REQUIRED_REPLAY_CHECKS, valid


class ReleaseExportError(RuntimeError):
    """A classified failure that must not publish a release."""

    def __init__(self, classification: str, message: str):
        super().__init__(message)
        self.classification = classification


class ReleaseNotExportableError(ReleaseExportError):
    """A valid pipeline terminal state that contains no releasable win."""


def _fail(classification: str, message: str) -> None:
    raise ReleaseExportError(classification, message)


def _safe_run_id(value: Any) -> str:
    if not isinstance(value, str) or not _RUN_ID_PATTERN.fullmatch(value):
        _fail(
            "INVALID_RUN_ID",
            "run_id must match [A-Za-z0-9][A-Za-z0-9_.-]{0,127}",
        )
    return value


def _is_lower_sha256(value: Any) -> bool:
    return isinstance(value, str) and _LOWER_SHA256_PATTERN.fullmatch(value) is not None


def _strict_json_loads(text: str, *, source: Path) -> Any:
    def object_without_duplicates(
        pairs: Iterable[tuple[str, Any]],
    ) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON object key: {key!r}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number: {value}")

    try:
        return json.loads(
            text,
            object_pairs_hook=object_without_duplicates,
            parse_constant=reject_constant,
        )
    except (json.JSONDecodeError, UnicodeError, ValueError) as exc:
        _fail("SOURCE_INVALID", f"invalid JSON in {source}: {exc}")


def _ensure_beneath(path: Path, root: Path, *, label: str) -> None:
    try:
        path.relative_to(root)
    except ValueError:
        _fail("UNSAFE_PATH", f"{label} escapes {root}: {path}")


def _reject_symlink_components(
    path: Path,
    *,
    root: Path,
    include_leaf: bool = True,
) -> None:
    """Reject every existing symlink between ``root`` and ``path``."""

    _ensure_beneath(path, root, label="path")
    relative = path.relative_to(root)
    parts = relative.parts if include_leaf else relative.parts[:-1]
    current = root
    for part in parts:
        current /= part
        try:
            metadata = current.lstat()
        except FileNotFoundError:
            continue
        except OSError as exc:
            _fail("UNSAFE_PATH", f"cannot inspect path component {current}: {exc}")
        if stat.S_ISLNK(metadata.st_mode):
            _fail("UNSAFE_PATH", f"path component may not be a symlink: {current}")


def _require_directory(path: Path, *, root: Path, label: str) -> None:
    _reject_symlink_components(path, root=root)
    try:
        metadata = path.lstat()
    except OSError as exc:
        _fail("SOURCE_INVALID", f"{label} directory is unavailable: {path}: {exc}")
    if not stat.S_ISDIR(metadata.st_mode):
        _fail("UNSAFE_PATH", f"{label} is not a directory: {path}")


def _read_regular_bytes(path: Path, *, root: Path, label: str) -> bytes:
    _reject_symlink_components(path, root=root, include_leaf=False)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        _fail("SOURCE_INVALID", f"{label} is unavailable: {path}: {exc}")
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            _fail("UNSAFE_PATH", f"{label} is not a regular file: {path}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    except OSError as exc:
        _fail("SOURCE_INVALID", f"cannot read {label} {path}: {exc}")
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _read_source_bytes_identity(
    path: Path,
    *,
    root: Path,
    label: str,
) -> tuple[bytes, dict[str, Any]]:
    """Read one source and bind metadata that detects restore-after-use."""

    _reject_symlink_components(path, root=root, include_leaf=False)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        _fail("SOURCE_INVALID", f"{label} is unavailable: {path}: {exc}")
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            _fail("UNSAFE_PATH", f"{label} is not a regular file: {path}")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            raw = stream.read()
            after = os.fstat(stream.fileno())
        fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns")
        if any(getattr(before, name) != getattr(after, name) for name in fields):
            _fail("SOURCE_INVALID", f"{label} changed while being read: {path}")
    except OSError as exc:
        _fail("SOURCE_INVALID", f"cannot read {label} {path}: {exc}")
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    return raw, {
        "sha256": _sha256_bytes(raw),
        "bytes": int(after.st_size),
        "mode": stat.S_IMODE(after.st_mode),
        "device": int(after.st_dev),
        "inode": int(after.st_ino),
        "mtime_ns": int(after.st_mtime_ns),
        "ctime_ns": int(after.st_ctime_ns),
    }


def _read_json_object(
    path: Path,
    *,
    root: Path,
    label: str,
) -> tuple[dict[str, Any], bytes]:
    raw = _read_regular_bytes(path, root=root, label=label)
    try:
        text = raw.decode("utf-8")
    except UnicodeError as exc:
        _fail("SOURCE_INVALID", f"{label} is not UTF-8: {path}: {exc}")
    value = _strict_json_loads(text, source=path)
    if not isinstance(value, dict):
        _fail("SOURCE_INVALID", f"{label} must contain a JSON object: {path}")
    return value, raw


def _read_jsonl_objects(
    path: Path,
    *,
    root: Path,
    label: str,
) -> tuple[list[dict[str, Any]], bytes]:
    raw = _read_regular_bytes(path, root=root, label=label)
    try:
        text = raw.decode("utf-8")
    except UnicodeError as exc:
        _fail("SOURCE_INVALID", f"{label} is not UTF-8: {path}: {exc}")
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            _fail(
                "SOURCE_INVALID",
                f"{label} contains a blank JSONL row at line {line_number}",
            )
        value = _strict_json_loads(line, source=path)
        if not isinstance(value, dict):
            _fail(
                "SOURCE_INVALID",
                f"{label} row {line_number} must be a JSON object",
            )
        rows.append(value)
    if not rows:
        _fail("SOURCE_INVALID", f"{label} contains no certificates")
    return rows, raw


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _is_untrusted_import_artifact(path: Path) -> bool:
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
    try:
        return Path(importlib.util.source_from_cache(str(cache)))
    except ValueError:
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


def _pyc_matches_current_source(cache: Path, source: Path) -> bool:
    """Accept an inert stale cache or bytecode identical to its bound source."""

    try:
        raw = _read_regular_bytes(
            cache,
            root=source.parent,
            label="Python bytecode cache",
        )
        if len(raw) < 16:
            return False
        if raw[:4] != importlib.util.MAGIC_NUMBER:
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
        source_bytes = _read_regular_bytes(
            source,
            root=source.parent,
            label="Python source",
        )
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
        OverflowError,
        RecursionError,
        ReleaseExportError,
        SyntaxError,
        TypeError,
        ValueError,
    ):
        return False


def _payload_sha256(value: Mapping[str, Any]) -> str:
    try:
        encoded = json.dumps(
            dict(value),
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode()
    except (TypeError, ValueError) as exc:
        _fail("SOURCE_INVALID", f"certificate payload cannot be hashed: {exc}")
    return hashlib.sha256(encoded).hexdigest()


def _pipeline_fingerprint(value: Any) -> str:
    try:
        encoded = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            default=str,
        ).encode()
    except (TypeError, ValueError) as exc:
        _fail(
            "SOURCE_INVALID",
            f"pipeline provenance cannot be hashed: {exc}",
        )
    return hashlib.sha256(encoded).hexdigest()


def _source_fingerprint(
    repo: Path,
    *roots: Path,
) -> tuple[str, dict[Path, bytes]]:
    """Independently hash the exact Stage 5 implementation dependency tree."""

    files: set[Path] = set()
    for path in roots:
        _ensure_beneath(path, repo, label="Stage 5 source dependency")
        _reject_symlink_components(path, root=repo)
        try:
            metadata = path.lstat()
        except OSError as exc:
            _fail(
                "SOURCE_INVALID",
                f"Stage 5 source dependency is unavailable: {path}: {exc}",
            )
        if stat.S_ISDIR(metadata.st_mode):
            for item in sorted(path.rglob("*")):
                _reject_symlink_components(item, root=repo)
                try:
                    item_metadata = item.lstat()
                except OSError as exc:
                    _fail(
                        "SOURCE_INVALID",
                        f"cannot inspect Stage 5 source tree entry {item}: {exc}",
                    )
                if stat.S_ISREG(item_metadata.st_mode):
                    if item.suffix == ".py":
                        files.add(item)
                    elif _is_untrusted_import_artifact(item):
                        _fail(
                            "UNSAFE_PATH",
                            "Stage 5 source tree contains an unhashed executable "
                            f"Python import artifact: {item}",
                        )
                elif not stat.S_ISDIR(item_metadata.st_mode):
                    _fail(
                        "UNSAFE_PATH",
                        "Stage 5 source tree entry is not a regular file or "
                        f"directory: {item}",
                    )
        elif stat.S_ISREG(metadata.st_mode):
            if _is_untrusted_import_artifact(path):
                _fail(
                    "UNSAFE_PATH",
                    "Stage 5 source dependency is an untrusted executable "
                    f"Python import artifact: {path}",
                )
            files.add(path)
        else:
            _fail(
                "UNSAFE_PATH",
                f"Stage 5 source dependency is not a regular file or directory: {path}",
            )

    raw_by_path: dict[Path, bytes] = {}
    identities: dict[str, dict[str, Any]] = {}
    for path in sorted(files):
        raw, identity = _read_source_bytes_identity(
            path,
            root=repo,
            label="Stage 5 source dependency",
        )
        raw_by_path[path] = raw
        identities[str(path)] = identity
    fingerprint = _pipeline_fingerprint(identities)
    return fingerprint, raw_by_path


def _positive_config_number(
    config: Mapping[str, Any],
    name: str,
) -> int | float:
    value = config.get(name)
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or value <= 0
    ):
        _fail("STATE_INVALID", f"pipeline config {name} must be positive and finite")
    return value


def _validate_current_stage5_provenance(
    *,
    record: Mapping[str, Any],
    config: Mapping[str, Any],
    repo: Path,
    pipeline_root: Path,
    stage4_certificates_path: Path,
    stage5_path: Path,
    controller_source_sha256: str,
    source_fingerprint: str,
    known_code_registry_sha256: str,
    strict_runner_sha256: str,
    proof_runtime: Mapping[str, Any],
    proof_interpreter: Mapping[str, Any],
) -> dict[str, Any]:
    python_executable = config.get("python_executable")
    configured_resume = config.get("resume")
    solver_workers = config.get("certificate_solver_workers")
    if not isinstance(python_executable, str) or not python_executable:
        _fail("STATE_INVALID", "pipeline config python_executable is invalid")
    if not isinstance(configured_resume, bool):
        _fail("STATE_INVALID", "pipeline config resume must be boolean")
    if (
        isinstance(solver_workers, bool)
        or not isinstance(solver_workers, int)
        or solver_workers <= 0
    ):
        _fail(
            "STATE_INVALID",
            "pipeline config certificate_solver_workers must be positive",
        )
    base_known_answer_timeout = _positive_config_number(
        config, "known_answer_timeout_per_logical"
    )
    base_known_answer_total_timeout = _positive_config_number(
        config, "known_answer_total_timeout"
    )
    base_verification_timeout = _positive_config_number(
        config, "verification_timeout_per_logical"
    )
    base_verification_total_timeout = _positive_config_number(
        config, "verification_total_timeout"
    )
    stage_config = record.get("stage_config")
    if not isinstance(stage_config, Mapping):
        _fail(
            "STAGE5_PROVENANCE_MISMATCH",
            "Stage 5 stage_config must be an object",
        )
    # Stage 5 records created before the proof-retry resume binding was added
    # used the top-level campaign setting directly.  Preserve validation of
    # those records, while requiring any explicitly recorded effective value
    # to be a boolean and binding it into both command and fingerprint.
    has_effective_resume = "effective_resume" in stage_config
    effective_resume = stage_config.get(
        "effective_resume",
        configured_resume,
    )
    if not isinstance(effective_resume, bool):
        _fail(
            "STAGE5_PROVENANCE_MISMATCH",
            "Stage 5 effective_resume must be boolean",
        )
    raw_multiplier = stage_config.get("proof_budget_multiplier", 1.0)
    configured_max_multiplier = config.get("proof_retry_max_multiplier", 1.0)
    if (
        isinstance(raw_multiplier, bool)
        or not isinstance(raw_multiplier, (int, float))
        or not math.isfinite(float(raw_multiplier))
        or float(raw_multiplier) < 1.0
        or isinstance(configured_max_multiplier, bool)
        or not isinstance(configured_max_multiplier, (int, float))
        or not math.isfinite(float(configured_max_multiplier))
        or float(configured_max_multiplier) < 1.0
        or float(raw_multiplier) > float(configured_max_multiplier)
    ):
        _fail(
            "STAGE5_PROVENANCE_MISMATCH",
            "Stage 5 proof retry multiplier is outside the configured budget",
        )
    multiplier = float(raw_multiplier)
    known_answer_timeout = (
        base_known_answer_timeout
        if multiplier == 1.0
        else max(1, math.ceil(float(base_known_answer_timeout) * multiplier))
    )
    known_answer_total_timeout = (
        base_known_answer_total_timeout
        if multiplier == 1.0
        else max(
            1,
            math.ceil(float(base_known_answer_total_timeout) * multiplier),
        )
    )
    verification_timeout = (
        base_verification_timeout
        if multiplier == 1.0
        else float(base_verification_timeout) * multiplier
    )
    verification_total_timeout = (
        base_verification_total_timeout
        if multiplier == 1.0
        else float(base_verification_total_timeout) * multiplier
    )
    known_answer_path = repo / "results" / "known_answer_gate.json"
    trust_path = repo / "results" / "known_answer_trust.json"
    finalizer_path = repo / "scripts" / "finalize_challenge.py"
    expected_command = [
        python_executable,
        "-I",
        "-B",
        str(finalizer_path),
        str(stage4_certificates_path),
        "--known-answer-artifact",
        str(known_answer_path),
        "--known-answer-trust",
        str(trust_path),
        "--known-answer-timeout-per-logical",
        str(known_answer_timeout),
        "--known-answer-total-timeout",
        str(known_answer_total_timeout),
        "--verification-timeout-per-logical",
        str(verification_timeout),
        "--verification-total-timeout",
        str(verification_total_timeout),
        "--verification-solver-workers",
        str(solver_workers),
        "--verification-state-dir",
        str(pipeline_root / "solver-state" / "strict-verification"),
        "--resume" if effective_resume else "--no-resume",
        "--output",
        str(stage5_path),
    ]
    expected_stage_config = {
        "controller_source_sha256": controller_source_sha256,
        "mode": "strict",
        "source_fingerprint": source_fingerprint,
        "known_code_registry_sha256": known_code_registry_sha256,
        "strict_runner_sha256": strict_runner_sha256,
        "proof_runtime": dict(proof_runtime),
        "proof_interpreter": dict(proof_interpreter),
        "known_answer_timeout_per_logical": known_answer_timeout,
        "known_answer_total_timeout": known_answer_total_timeout,
        "verification_timeout_per_logical": verification_timeout,
        "verification_total_timeout": verification_total_timeout,
        "verification_solver_workers": solver_workers,
    }
    if has_effective_resume:
        expected_stage_config["effective_resume"] = effective_resume
    if multiplier != 1.0:
        expected_stage_config["proof_budget_multiplier"] = multiplier
    if record.get("command") != expected_command:
        _fail(
            "STAGE5_PROVENANCE_MISMATCH",
            "Stage 5 command does not match the current strict production command",
        )
    if record.get("stage_config") != expected_stage_config:
        _fail(
            "STAGE5_PROVENANCE_MISMATCH",
            "Stage 5 stage_config does not match current trusted dependencies",
        )
    expected_fingerprint = _pipeline_fingerprint(
        {
            "command": expected_command,
            "stage_config": expected_stage_config,
        }
    )
    if record.get("stage_fingerprint") != expected_fingerprint:
        _fail(
            "STAGE5_PROVENANCE_MISMATCH",
            "Stage 5 fingerprint does not bind its exact command and stage_config",
        )
    return {
        "controller_source_sha256": controller_source_sha256,
        "source_fingerprint": source_fingerprint,
        "known_code_registry_sha256": known_code_registry_sha256,
        "strict_runner_sha256": strict_runner_sha256,
        "proof_runtime": dict(proof_runtime),
        "proof_interpreter": dict(proof_interpreter),
    }


def _require_schema_one(value: Mapping[str, Any], *, label: str) -> None:
    schema = value.get("schema_version")
    if isinstance(schema, bool) or not isinstance(schema, int) or schema != 1:
        _fail("SOURCE_INVALID", f"{label} schema_version must be integer 1")


def _positive_integer(value: Any, *, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        _fail("WIN_EVIDENCE_INVALID", f"{label} must be a positive integer")
    return value


def _matching_fom(value: Any, expected: float, *, label: str) -> None:
    valid = (
        not isinstance(value, bool)
        and isinstance(value, (int, float))
        and math.isfinite(float(value))
        and math.isclose(float(value), expected, rel_tol=0.0, abs_tol=1e-9)
    )
    if not valid:
        _fail("WIN_EVIDENCE_INVALID", f"{label} does not match k*d^2/n")


def _validate_win_gate(
    claim: Mapping[str, Any],
    gate: Any,
    *,
    label: str,
) -> int:
    n = _positive_integer(claim.get("n"), label=f"{label} claim.n")
    k = _positive_integer(claim.get("k"), label=f"{label} claim.k")
    d = _positive_integer(claim.get("d"), label=f"{label} claim.d")
    expected = classify_win(n, k, d)
    if expected.get("passed") is not True:
        _fail(
            "NOT_A_CHALLENGE_WIN",
            f"{label} claim [[{n},{k},{d}]] does not satisfy a challenge win rule",
        )
    _matching_fom(
        claim.get("fom"),
        expected["fom"],
        label=f"{label} claim.fom",
    )
    if not isinstance(gate, dict) or gate.get("accepted") is not True:
        _fail("WIN_EVIDENCE_INVALID", f"{label} final_gate is not accepted")
    checks = gate.get("checks")
    if (
        not isinstance(checks, dict)
        or not checks
        or any(value is not True for value in checks.values())
        or gate.get("failures") != []
    ):
        _fail(
            "WIN_EVIDENCE_INVALID",
            f"{label} final_gate checks/failures are inconsistent",
        )
    win = gate.get("win")
    if (
        not isinstance(win, dict)
        or win.get("passed") is not True
        or win.get("reasons") != expected["reasons"]
    ):
        _fail("WIN_EVIDENCE_INVALID", f"{label} final_gate.win is inconsistent")
    _matching_fom(
        win.get("fom"),
        expected["fom"],
        label=f"{label} final_gate.win.fom",
    )
    candidate = gate.get("candidate")
    if not isinstance(candidate, dict):
        _fail("WIN_EVIDENCE_INVALID", f"{label} final_gate.candidate is missing")
    for name, expected_value in (("n", n), ("k", k), ("d", d)):
        value = candidate.get(name)
        if (
            isinstance(value, bool)
            or not isinstance(value, int)
            or value != expected_value
        ):
            _fail(
                "WIN_EVIDENCE_INVALID",
                f"{label} final_gate.candidate.{name} is inconsistent",
            )
    _matching_fom(
        candidate.get("fom"),
        expected["fom"],
        label=f"{label} final_gate.candidate.fom",
    )
    return k


def _sector_sat_expected_lower_decisions(
    certificate: Mapping[str, Any],
) -> int:
    """Freshly replay an optional BB isometry and validate proof coverage.

    Release export is the last trust boundary.  It therefore reconstructs the
    BB matrices itself and never reduces X/Z coverage merely because a stored
    report says ``verified=true``.
    """

    claim = certificate.get("claim")
    sector_exact = certificate.get("sector_exact")
    proof = (
        claim.get("exact_distance_proof")
        if isinstance(claim, Mapping)
        else None
    )
    if not all(
        isinstance(value, Mapping) for value in (claim, sector_exact, proof)
    ):
        _fail("STAGE4_INVALID", "sector-SAT proof envelope is malformed")
    assert isinstance(claim, Mapping)
    assert isinstance(sector_exact, Mapping)
    assert isinstance(proof, Mapping)
    if any(
        "xz_sector_isometry" not in value
        for value in (certificate, sector_exact, proof)
    ):
        _fail(
            "STAGE4_INVALID",
            "sector-SAT proof does not explicitly bind all X/Z-isometry fields",
        )
    stored = proof.get("xz_sector_isometry")
    if not (
        certificate.get("xz_sector_isometry") == stored
        and sector_exact.get("xz_sector_isometry") == stored
    ):
        _fail(
            "STAGE4_INVALID",
            "sector-SAT X/Z-isometry reports differ across certificate layers",
        )

    k = _positive_integer(claim.get("k"), label="sector-SAT claim.k")
    mode = proof.get("coverage_mode")
    if mode not in {"global", "first-nonzero"}:
        _fail("STAGE4_INVALID", "sector-SAT coverage_mode is unsupported")
    if sector_exact.get("coverage_mode") != mode:
        _fail(
            "STAGE4_INVALID",
            "sector-SAT proof and certificate coverage modes differ",
        )

    if stored is None:
        sector_count = 2
    elif isinstance(stored, Mapping):
        try:
            ell = claim["ell"]
            m = claim["m"]
            if any(
                isinstance(value, bool)
                or not isinstance(value, int)
                or value <= 0
                for value in (ell, m)
            ):
                raise ValueError("BB lattice dimensions must be positive integers")
            n = _positive_integer(claim.get("n"), label="sector-SAT claim.n")
            code = build_bb_code(
                ell,
                m,
                claim["A_terms"],
                claim["B_terms"],
                geometry=candidate_geometry(claim),
            )
            hx, hz, _lx, _lz = get_code_matrices(code)
            replayed = verify_bb_xz_sector_isometry(
                hx,
                hz,
                ell=ell,
                m=m,
                geometry=candidate_geometry(claim),
            )
            geometry_matches = bool(
                int(code.num_qudits) == n
                and int(code.dimension) == k
            )
        except Exception as exc:
            _fail(
                "STAGE4_INVALID",
                f"sector-SAT X/Z-isometry replay failed: {exc}",
            )
        if not (
            geometry_matches
            and replayed.get("verified") is True
            and replayed.get("canonical_sector") == "X"
            and replayed.get("covered_sectors") == ["X", "Z"]
            and dict(stored) == replayed
        ):
            _fail(
                "STAGE4_INVALID",
                "stored sector-SAT X/Z-isometry report did not freshly replay",
            )
        sector_count = 1
    else:
        _fail(
            "STAGE4_INVALID",
            "sector-SAT X/Z-isometry field must be an object or null",
        )

    stored_cubes = proof.get("anchor_cover_cubes")
    if not (
        certificate.get("anchor_cover_cubes") == stored_cubes
        and sector_exact.get("anchor_cover_cubes") == stored_cubes
    ):
        _fail(
            "STAGE4_INVALID",
            "sector-SAT anchor-cover reports differ across certificate layers",
        )
    if stored_cubes is None:
        cube_count = 1
    elif isinstance(stored_cubes, list) and stored_cubes:
        try:
            from scripts.screen_frontier_sat import build_anchor_cover_cubes
            from scripts.screen_frontier_xor import (
                verify_bb_translation_symmetry,
            )

            symmetry = verify_bb_translation_symmetry(dict(claim))
            raw_anchors = proof.get("anchor_indices")
            if (
                symmetry.get("verified") is not True
                or proof.get("translation_symmetry") != symmetry
                or not isinstance(raw_anchors, list)
                or any(
                    isinstance(index, bool) or not isinstance(index, int)
                    for index in raw_anchors
                )
            ):
                raise ValueError("BB translation-anchor replay failed")
            anchors = tuple(raw_anchors)
            if anchors != tuple(
                int(index) for index in symmetry["orbit_representatives"]
            ):
                raise ValueError("stored BB translation anchors differ")
            replayed_cubes = build_anchor_cover_cubes(anchors)
        except Exception as exc:
            _fail(
                "STAGE4_INVALID",
                f"sector-SAT anchor-cover replay failed: {exc}",
            )
        if stored_cubes != replayed_cubes:
            _fail(
                "STAGE4_INVALID",
                "stored sector-SAT anchor cover did not freshly replay",
            )
        cube_count = len(replayed_cubes)
    else:
        _fail(
            "STAGE4_INVALID",
            "sector-SAT anchor_cover_cubes must be a nonempty list or null",
        )

    expected_partitions = sector_count * (1 if mode == "global" else k)
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
        _fail(
            "STAGE4_INVALID",
            "sector-SAT lower-decision count does not match replayed coverage",
        )
    if stored_cubes is not None and not (
        proof.get("expected_lower_partitions") == expected_partitions
        and proof.get("completed_lower_partitions") == expected_partitions
        and sector_exact.get("expected_lower_partitions")
        == expected_partitions
        and sector_exact.get("completed_lower_partitions")
        == expected_partitions
    ):
        _fail(
            "STAGE4_INVALID",
            "sector-SAT logical-partition count does not match anchor cover",
        )
    if stored_cubes is None:
        for value in (proof, sector_exact):
            if (
                "expected_lower_partitions" in value
                or "completed_lower_partitions" in value
            ) and not (
                value.get("expected_lower_partitions") == expected_partitions
                and value.get("completed_lower_partitions")
                == expected_partitions
            ):
                _fail(
                    "STAGE4_INVALID",
                    "legacy sector-SAT logical-partition counts are invalid",
                )
    return expected


def _require_exact_output_hashes(
    record: Any,
    actual: Mapping[Path, bytes],
    *,
    stage: str,
) -> dict[str, Any]:
    if not isinstance(record, dict):
        _fail("STATE_INVALID", f"state has no {stage} record")
    if record.get("machine_status") != "COMPLETED":
        _fail("STATE_INVALID", f"{stage} machine_status must be COMPLETED")
    if record.get("status") != "COMPLETED":
        _fail("STATE_INVALID", f"{stage} status must be COMPLETED")
    exit_code = record.get("exit_code")
    if isinstance(exit_code, bool) or not isinstance(exit_code, int) or exit_code != 0:
        _fail("STATE_INVALID", f"{stage} exit_code is not successful")
    output_hashes = record.get("output_hashes")
    if not isinstance(output_hashes, dict):
        _fail("STATE_INVALID", f"{stage} has no output_hashes object")
    expected_keys = {str(path) for path in actual}
    if set(output_hashes) != expected_keys:
        _fail(
            "STATE_HASH_MISMATCH",
            f"{stage} output_hashes do not name exactly the expected artifacts",
        )
    for path, raw in actual.items():
        expected = output_hashes.get(str(path))
        if not _is_lower_sha256(expected) or expected != _sha256_bytes(raw):
            _fail(
                "STATE_HASH_MISMATCH",
                f"{stage} output hash mismatch for {path}",
            )
    return record


def _require_exact_input_hashes(
    record: Mapping[str, Any],
    actual: Mapping[Path, bytes],
) -> None:
    input_hashes = record.get("input_hashes")
    if not isinstance(input_hashes, dict):
        _fail("STATE_INVALID", f"{_STAGE5} has no input_hashes object")
    expected_keys = {str(path) for path in actual}
    if set(input_hashes) != expected_keys:
        _fail(
            "STATE_HASH_MISMATCH",
            "Stage 5 input_hashes do not name exactly the expected artifacts",
        )
    for path, raw in actual.items():
        recorded = input_hashes.get(str(path))
        if not _is_lower_sha256(recorded) or recorded != _sha256_bytes(raw):
            _fail(
                "STATE_HASH_MISMATCH",
                f"Stage 5 input hash mismatch for {path}",
            )


def _resolve_solver_file(
    value: Any,
    *,
    solver_root: Path,
    label: str,
) -> Path:
    if not isinstance(value, str) or not value:
        _fail("SOURCE_INVALID", f"{label} must be a non-empty path string")
    path = Path(value)
    if not path.is_absolute() or ".." in path.parts:
        _fail("UNSAFE_PATH", f"{label} must be an absolute normalized path")
    _ensure_beneath(path, solver_root, label=label)
    _reject_symlink_components(path, root=solver_root)
    return path


def _validate_trust(
    trust: Mapping[str, Any],
    *,
    artifact_sha256: str,
    proof_runtime: Mapping[str, Any],
) -> None:
    _require_schema_one(trust, label="known-answer trust")
    if not _is_lower_sha256(trust.get("artifact_sha256")):
        _fail("TRUST_INVALID", "known-answer trust artifact_sha256 is invalid")
    if trust.get("artifact_sha256") != artifact_sha256:
        _fail(
            "TRUST_INVALID",
            "repository-pinned known-answer artifact SHA-256 does not match the file",
        )
    if not _is_lower_sha256(trust.get("semantic_sha256")):
        _fail("TRUST_INVALID", "known-answer trust semantic_sha256 is invalid")
    if not isinstance(trust.get("environment"), dict):
        _fail("TRUST_INVALID", "known-answer trust environment must be an object")
    try:
        current_environment = known_answer_environment(proof_runtime)
    except ValueError as exc:
        _fail("RUNTIME_INVALID", f"current proof runtime is invalid: {exc}")
    if _payload_sha256(trust["environment"]) != _payload_sha256(
        current_environment
    ):
        _fail(
            "TRUST_INVALID",
            "known-answer trust environment differs from current proof runtime",
        )


def _validate_integrity(
    integrity: Any,
    *,
    trust: Mapping[str, Any],
) -> dict[str, Any]:
    if not isinstance(integrity, dict):
        _fail("STAGE5_INVALID", "Stage 5 known_answer_integrity must be an object")
    if integrity.get("passed") is not True or integrity.get("mode") != "strict":
        _fail(
            "STAGE5_INVALID",
            "Stage 5 known-answer integrity must be a passed strict replay",
        )
    artifact_sha = integrity.get("artifact_sha256")
    semantic_sha = integrity.get("semantic_sha256")
    rerun_sha = integrity.get("rerun_semantic_sha256")
    if not all(
        _is_lower_sha256(item)
        for item in (
            artifact_sha,
            semantic_sha,
            rerun_sha,
        )
    ):
        _fail("STAGE5_INVALID", "Stage 5 strict provenance SHA-256 is invalid")
    integrity_environment = integrity.get("environment")
    trust_environment = trust.get("environment")
    if (
        artifact_sha != trust.get("artifact_sha256")
        or semantic_sha != trust.get("semantic_sha256")
        or rerun_sha != trust.get("semantic_sha256")
        or semantic_sha != rerun_sha
        or not isinstance(integrity_environment, dict)
        or not isinstance(trust_environment, dict)
        or _payload_sha256(integrity_environment) != _payload_sha256(trust_environment)
    ):
        _fail(
            "STAGE5_INVALID",
            "Stage 5 strict provenance differs from repository-pinned trust",
        )
    if integrity.get("failures") != []:
        _fail("STAGE5_INVALID", "passed Stage 5 integrity contains failures")
    return integrity


def _validate_twobga_exact_evidence(
    certificate: Mapping[str, Any],
    claim: Mapping[str, Any],
    *,
    index: int,
) -> None:
    """Validate the typed 2BGA theorem bridge without inventing 2k lanes."""

    exact = certificate.get("twobga_exact")
    proof = claim.get("exact_distance_proof")
    theorem = certificate.get("theorem_eligibility")
    if (
        "milp" in certificate
        or "sector_exact" in certificate
        or certificate.get("candidate_rejection") is not None
        or certificate.get("formulation") != _TWOBGA_FORMULATION
        or certificate.get("independent_verification_required") is not True
        or certificate.get("build_assurance")
        != "provisional-structural-replay"
        or not isinstance(exact, Mapping)
        or not isinstance(proof, Mapping)
        or not isinstance(theorem, Mapping)
        or exact.get("exact") is not True
        or claim.get("d_is_exact") is not True
        or proof.get("exact") is not True
        or isinstance(proof.get("schema_version"), bool)
        or proof.get("schema_version") != 1
        or proof.get("proof_type") != _TWOBGA_EXACT_PROOF_TYPE
        or proof.get("subsystem_distance_semantics")
        != "dressed-logical-center-quotient"
        or proof.get("required_auxiliary_sectors") != ["X", "Z"]
        or theorem.get("eligible") is not True
        or proof.get("theorem_eligibility") != theorem
        or exact.get("proof") != proof
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] lacks typed exact 2BGA evidence",
        )

    distance = claim.get("d")
    integer_bounds = (
        distance,
        exact.get("required_distance"),
        exact.get("distance"),
        exact.get("lower_bound"),
        exact.get("upper_bound"),
        proof.get("required_distance"),
        proof.get("distance"),
        proof.get("lower_bound_threshold"),
        proof.get("lower_bound"),
        proof.get("upper_bound"),
        exact.get("expected_lower_decisions"),
        exact.get("completed_lower_decisions"),
    )
    if (
        any(
            isinstance(value, bool) or not isinstance(value, int)
            for value in integer_bounds
        )
        or exact.get("required_distance") != distance
        or exact.get("distance") != distance
        or exact.get("lower_bound") != distance
        or exact.get("upper_bound") != distance
        or exact.get("expected_lower_decisions") != 2
        or exact.get("completed_lower_decisions") != 2
        or proof.get("required_distance") != distance
        or proof.get("distance") != distance
        or proof.get("lower_bound_threshold") != distance - 1
        or proof.get("lower_bound") != distance
        or proof.get("upper_bound") != distance
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] 2BGA exact bounds are inconsistent",
        )

    lower = proof.get("lower_bound_decisions")
    if not (
        isinstance(lower, list)
        and len(lower) == 2
        and all(isinstance(item, Mapping) for item in lower)
        and [item.get("sector") for item in lower] == ["X", "Z"]
        and all(
            item.get("unit_id") == f"aux-lower-{sector}"
            and item.get("domain") == "auxiliary-subsystem"
            and item.get("phase") == "lower"
            and item.get("max_weight") == distance - 1
            and isinstance(item.get("anchor_indices"), list)
            and all(
                isinstance(anchor, int) and not isinstance(anchor, bool)
                for anchor in item["anchor_indices"]
            )
            and isinstance(item.get("solver_evidence"), Mapping)
            for item, sector in zip(lower, ("X", "Z"), strict=True)
        )
        and exact.get("lower_bound_decisions") == lower
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] 2BGA lower-bound decisions are inconsistent",
        )

    upper = proof.get("upper_witness")
    if not (
        isinstance(upper, Mapping)
        and upper.get("unit_id") == "original-upper-X"
        and upper.get("domain") == "original-code"
        and upper.get("phase") == "upper"
        and upper.get("sector") == "X"
        and upper.get("max_weight") == distance
        and isinstance(upper.get("anchor_indices"), list)
        and all(
            isinstance(anchor, int) and not isinstance(anchor, bool)
            for anchor in upper["anchor_indices"]
        )
        and upper.get("witness_verified") is True
        and upper.get("witness_failures") == []
        and isinstance(upper.get("solver_evidence"), Mapping)
        and exact.get("upper_witness") == upper
        and exact.get("upper_attempt") in (None, upper)
        and isinstance(proof.get("original_logical_detector"), Mapping)
        and isinstance(proof.get("original_translation_symmetry"), Mapping)
        and isinstance(proof.get("original_anchor_indices"), list)
        and all(
            isinstance(anchor, int) and not isinstance(anchor, bool)
            for anchor in proof["original_anchor_indices"]
        )
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] 2BGA upper witness is inconsistent",
        )

    matrix_sha = certificate.get("matrix_sha256")
    if not (
        isinstance(matrix_sha, Mapping)
        and set(matrix_sha) == {"hx", "hz"}
        and all(_is_lower_sha256(matrix_sha[name]) for name in ("hx", "hz"))
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] 2BGA matrix binding is invalid",
        )
    try:
        proof_sha = canonical_sha256(dict(proof), omit="proof_sha256")
    except (TypeError, ValueError) as exc:
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] 2BGA proof cannot be hashed: {exc}",
        )
    if (
        not _is_lower_sha256(proof.get("proof_sha256"))
        or proof.get("proof_sha256") != proof_sha
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] 2BGA proof SHA-256 mismatch",
        )


def _validate_certificate(
    certificate: Mapping[str, Any],
    *,
    index: int,
    known_answer_sha256: str,
) -> str:
    _require_schema_one(certificate, label=f"certificate[{index}]")
    if certificate.get("certificate_type") not in _SUPPORTED_CERTIFICATE_TYPES:
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] has an unsupported certificate_type",
        )
    if certificate.get("passed") is not True:
        _fail("STAGE4_INVALID", f"certificate[{index}] did not pass")
    claim = certificate.get("claim")
    if not isinstance(claim, dict):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] lacks a claim object",
        )
    k = _validate_win_gate(
        claim,
        certificate.get("final_gate"),
        label=f"certificate[{index}]",
    )
    known_answer = certificate.get("known_answer")
    if (
        not isinstance(known_answer, dict)
        or known_answer.get("artifact_sha256") != known_answer_sha256
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] is not bound to the pinned known answer",
        )
    certificate_type = certificate.get("certificate_type")
    if certificate_type == _TWOBGA_CERTIFICATE_TYPE:
        _validate_twobga_exact_evidence(
            certificate,
            claim,
            index=index,
        )
    elif certificate_type == _SECTOR_SAT_CERTIFICATE_TYPE:
        sector_exact = certificate.get("sector_exact")
        proof = claim.get("exact_distance_proof")
        if (
            "milp" in certificate
            or not isinstance(sector_exact, dict)
            or not isinstance(proof, dict)
            or sector_exact.get("exact") is not True
            or proof.get("proof_type") != "qldpc-css-sector-sat-exact-proof-v1"
            or proof.get("exact") is not True
        ):
            _fail(
                "STAGE4_INVALID",
                f"certificate[{index}] lacks typed exact sector-SAT evidence",
            )
        contract_expected = _sector_sat_expected_lower_decisions(certificate)
        distance = sector_exact.get("distance")
        expected = sector_exact.get("expected_lower_decisions")
        completed = sector_exact.get("completed_lower_decisions")
        if (
            isinstance(distance, bool)
            or not isinstance(distance, int)
            or distance != claim["d"]
            or sector_exact.get("lower_bound") != distance
            or sector_exact.get("upper_bound") != distance
            or proof.get("distance") != distance
            or proof.get("lower_bound") != distance
            or proof.get("upper_bound") != distance
            or isinstance(expected, bool)
            or not isinstance(expected, int)
            or expected != contract_expected
            or isinstance(completed, bool)
            or not isinstance(completed, int)
            or completed != expected
        ):
            _fail(
                "STAGE4_INVALID",
                f"certificate[{index}] sector-SAT bounds/counts are inconsistent",
            )
    else:
        milp = certificate.get("milp")
        if not isinstance(milp, dict):
            _fail(
                "STAGE4_INVALID",
                f"certificate[{index}] lacks MILP evidence",
            )
        distance = milp.get("distance")
        if (
            isinstance(distance, bool)
            or not isinstance(distance, int)
            or distance != claim["d"]
        ):
            _fail("STAGE4_INVALID", f"certificate[{index}] distance mismatch")
        expected = milp.get("expected_directions")
        completed = milp.get("completed_directions")
        if any(
            isinstance(item, bool) or not isinstance(item, int)
            for item in (k, expected, completed)
        ):
            _fail(
                "STAGE4_INVALID",
                f"certificate[{index}] direction counts must be integers",
            )
        directions = milp.get("directions")
        if (
            not isinstance(directions, list)
            or len(directions) != 2 * k
            or any(not isinstance(item, dict) for item in directions)
        ):
            _fail(
                "STAGE4_INVALID",
                f"certificate[{index}] must contain exactly 2k direction objects",
            )
        if (
            k <= 0
            or milp.get("exact") is not True
            or expected != completed
            or expected != 2 * k
        ):
            _fail(
                "STAGE4_INVALID",
                f"certificate[{index}] is not an exact complete 2k proof",
            )
    try:
        actual_sha = canonical_sha256(
            dict(certificate),
            omit="certificate_sha256",
        )
    except (TypeError, ValueError) as exc:
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] cannot be canonically hashed: {exc}",
        )
    if (
        not _is_lower_sha256(certificate.get("certificate_sha256"))
        or certificate.get("certificate_sha256") != actual_sha
    ):
        _fail(
            "STAGE4_INVALID",
            f"certificate[{index}] self SHA-256 mismatch",
        )
    return actual_sha


def _validate_stage4(
    *,
    summary: Mapping[str, Any],
    certificates: list[dict[str, Any]],
    certificates_path: Path,
    pipeline_root: Path,
    known_answer_sha256: str,
) -> list[str]:
    _require_schema_one(summary, label="Stage 4 summary")
    if (
        summary.get("gate") != "qcode-five-stage-certificate-merge"
        or summary.get("passed") is not True
        or summary.get("routing") != "STRICT_GATE"
    ):
        _fail("STAGE4_INVALID", "Stage 4 is not a passed STRICT_GATE merge")
    count = summary.get("verified_certificates")
    if (
        isinstance(count, bool)
        or not isinstance(count, int)
        or count <= 0
        or count != len(certificates)
    ):
        _fail("STAGE4_INVALID", "Stage 4 verified certificate count is invalid")
    if summary.get("certificate_output") != str(certificates_path):
        _fail(
            "STAGE4_INVALID",
            "Stage 4 certificate_output does not name its fixed artifact",
        )
    entries = summary.get("entries")
    if not isinstance(entries, list) or len(entries) != count:
        _fail("STAGE4_INVALID", "Stage 4 entries do not match its certificates")

    solver_root = pipeline_root / "solver-state"
    _require_directory(solver_root, root=pipeline_root, label="solver-state")
    hashes: list[str] = []
    seen: set[str] = set()
    for index, (certificate, entry) in enumerate(zip(certificates, entries)):
        if not isinstance(entry, dict):
            _fail("STAGE4_INVALID", f"Stage 4 entry[{index}] is malformed")
        certificate_sha = _validate_certificate(
            certificate,
            index=index,
            known_answer_sha256=known_answer_sha256,
        )
        if certificate_sha in seen:
            _fail("STAGE4_INVALID", f"duplicate certificate SHA-256 at index {index}")
        seen.add(certificate_sha)
        hashes.append(certificate_sha)
        if entry.get("certificate_sha256") != certificate_sha:
            _fail(
                "STAGE4_INVALID",
                f"Stage 4 entry[{index}] certificate SHA-256 mismatch",
            )
        payload_sha = _payload_sha256(certificate)
        if entry.get("certificate_payload_sha256") != payload_sha:
            _fail(
                "STAGE4_INVALID",
                f"Stage 4 entry[{index}] payload SHA-256 mismatch",
            )
        if entry.get("source_stage") not in {
            "stage2_sector_audit",
            "stage3_direction_audit",
        }:
            _fail("STAGE4_INVALID", f"Stage 4 entry[{index}] source is invalid")
        canonical_digest = entry.get("canonical_digest")
        if not isinstance(canonical_digest, str) or not canonical_digest:
            _fail(
                "STAGE4_INVALID",
                f"Stage 4 entry[{index}] canonical_digest is invalid",
            )

        certificate_path = _resolve_solver_file(
            entry.get("certificate_path"),
            solver_root=solver_root,
            label=f"Stage 4 entry[{index}] certificate_path",
        )
        original, original_raw = _read_json_object(
            certificate_path,
            root=solver_root,
            label=f"Stage 4 source certificate[{index}]",
        )
        if _payload_sha256(original) != payload_sha or entry.get(
            "file_sha256"
        ) != _sha256_bytes(original_raw):
            _fail(
                "STAGE4_INVALID",
                f"Stage 4 source certificate[{index}] differs from the merged row",
            )

        verification_path = _resolve_solver_file(
            entry.get("verification_path"),
            solver_root=solver_root,
            label=f"Stage 4 entry[{index}] verification_path",
        )
        envelope, envelope_raw = _read_json_object(
            verification_path,
            root=solver_root,
            label=f"Stage 4 verification sidecar[{index}]",
        )
        verification = envelope.get("verification")
        if (
            entry.get("verification_file_sha256") != _sha256_bytes(envelope_raw)
            or envelope.get("schema_version")
            != CERTIFICATE_CACHE_SCHEMA_VERSION
            or envelope.get("kind") != "qldpc-certificate-verification-cache"
            or envelope.get("canonical_digest") != canonical_digest
            or envelope.get("known_answer_sha256") != known_answer_sha256
            or envelope.get("certificate_sha256") != certificate_sha
            or envelope.get("certificate_payload_sha256") != payload_sha
            or not isinstance(verification, dict)
            or verification.get("passed") is not True
        ):
            _fail(
                "STAGE4_INVALID",
                f"Stage 4 verification sidecar[{index}] is not bound and passed",
            )
        if certificate.get("certificate_type") == _TWOBGA_CERTIFICATE_TYPE:
            checks = verification.get("checks")
            required_checks, replay_counts_valid = _strict_replay_contract(
                certificate,
                verification,
                k=certificate["claim"]["k"],
            )
            distance = verification.get("distance")
            verification_gate = verification.get("final_gate")
            if (
                verification.get("replay_complete") is not True
                or not isinstance(checks, Mapping)
                or not required_checks.issubset(checks)
                or any(value is not True for value in checks.values())
                or verification.get("failures") != []
                or isinstance(distance, bool)
                or not isinstance(distance, int)
                or distance != certificate["claim"]["d"]
                or not isinstance(verification_gate, Mapping)
                or _payload_sha256(dict(verification_gate))
                != _payload_sha256(certificate["final_gate"])
                or not replay_counts_valid
            ):
                _fail(
                    "STAGE4_INVALID",
                    "Stage 4 typed 2BGA verification sidecar"
                    f"[{index}] is incomplete or inconsistent",
                )
    return hashes


def _validate_stage5(
    *,
    gate: Mapping[str, Any],
    certificates: list[dict[str, Any]],
    certificate_hashes: list[str],
    trust: Mapping[str, Any],
) -> tuple[
    dict[str, Any],
    list[int],
    list[dict[str, Any]],
    dict[str, int],
]:
    _require_schema_one(gate, label="Stage 5 final gate")
    if (
        gate.get("gate") != "qldpc-challenge-final-batch"
        or gate.get("passed") is not True
        or gate.get("outcome") != "WIN"
    ):
        _fail("STAGE5_INVALID", "Stage 5 strict final gate is not a WIN")
    integrity = _validate_integrity(
        gate.get("known_answer_integrity"),
        trust=trust,
    )
    evaluations = gate.get("evaluations")
    summary = gate.get("summary")
    count = len(certificates)
    if not isinstance(evaluations, list) or len(evaluations) != count:
        _fail(
            "STAGE5_INVALID",
            "Stage 5 evaluations do not match the Stage 4 certificate count",
        )
    if not isinstance(summary, dict):
        _fail("STAGE5_INVALID", "Stage 5 summary must be an object")
    counts = {
        name: summary.get(name)
        for name in ("accepted", "rejected", "incomplete", "total")
    }
    if any(
        isinstance(item, bool) or not isinstance(item, int) or item < 0
        for item in counts.values()
    ):
        _fail("STAGE5_INVALID", "Stage 5 summary counts are invalid")
    if (
        counts["total"] != count
        or counts["accepted"] <= 0
        or counts["accepted"] + counts["rejected"] + counts["incomplete"] != count
    ):
        _fail("STAGE5_INVALID", "Stage 5 summary counts are inconsistent")

    accepted_indices: list[int] = []
    verifications: list[dict[str, Any]] = []
    observed = {"ACCEPTED": 0, "REJECTED": 0, "INCOMPLETE": 0}
    for index, (evaluation, certificate, certificate_sha) in enumerate(
        zip(evaluations, certificates, certificate_hashes)
    ):
        if not isinstance(evaluation, dict):
            _fail("STAGE5_INVALID", f"Stage 5 evaluation[{index}] is malformed")
        result = evaluation.get("result")
        disposition = evaluation.get("disposition")
        evaluation_claim = evaluation.get("claim")
        certificate_claim = certificate.get("claim")
        if (
            evaluation.get("source_index") != index
            or isinstance(evaluation.get("source_index"), bool)
            or evaluation.get("certificate_sha256") != certificate_sha
            or evaluation.get("certificate_payload_sha256")
            != canonical_sha256(dict(certificate))
            or not isinstance(evaluation_claim, dict)
            or not isinstance(certificate_claim, dict)
            or _payload_sha256(evaluation_claim) != _payload_sha256(certificate_claim)
            or not isinstance(result, dict)
            or disposition not in observed
        ):
            _fail(
                "STAGE5_BINDING_MISMATCH",
                f"Stage 5 evaluation[{index}] is not bound to Stage 4 certificate[{index}]",
            )
        observed[str(disposition)] += 1
        failures = result.get("failures")
        if disposition == "INCOMPLETE":
            try:
                failure_disposition = validate_failure_disposition(
                    result.get("failure_disposition"),
                )
            except ValueError:
                _fail(
                    "STAGE5_INVALID",
                    f"Stage 5 evaluation[{index}] lacks a typed retry reason",
                )
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
                _fail(
                    "STAGE5_INVALID",
                    f"Stage 5 evaluation[{index}] incomplete evidence is invalid",
                )
            continue
        if disposition == "REJECTED":
            _fail(
                "STAGE5_INVALID",
                "Stage 5 cannot terminally reject a Stage 4 certificate "
                f"that already passed build and independent replay: {index}",
            )
        final_gate = result.get("final_gate")
        certificate_gate = certificate.get("final_gate")
        if (
            result.get("passed") is not True
            or result.get("replay_complete") is not True
            or not isinstance(final_gate, dict)
            or not isinstance(certificate_gate, dict)
            or _payload_sha256(final_gate) != _payload_sha256(certificate_gate)
        ):
            _fail(
                "STAGE5_BINDING_MISMATCH",
                f"Stage 5 evaluation[{index}] accepted result is not bound",
            )
        checks = result.get("checks")
        k = certificate_claim["k"]
        distance = result.get("distance")
        required_checks, replay_counts_valid = _strict_replay_contract(
            certificate,
            result,
            k=k,
        )
        replay_distance_valid = bool(
            isinstance(distance, int)
            and not isinstance(distance, bool)
            and distance == certificate_claim["d"]
        )
        if (
            not isinstance(checks, dict)
            or not checks
            or not required_checks.issubset(checks)
            or any(value is not True for value in checks.values())
            or failures != []
            or not replay_distance_valid
            or not replay_counts_valid
        ):
            _fail(
                "STAGE5_INVALID",
                f"Stage 5 evaluation[{index}] replay evidence is inconsistent",
            )
        _validate_win_gate(
            certificate_claim,
            final_gate,
            label=f"Stage 5 evaluation[{index}]",
        )
        accepted_indices.append(index)
        verifications.append(result)
    if (
        observed["ACCEPTED"] != counts["accepted"]
        or observed["REJECTED"] != counts["rejected"]
        or observed["INCOMPLETE"] != counts["incomplete"]
        or len(accepted_indices) != counts["accepted"]
    ):
        _fail("STAGE5_INVALID", "Stage 5 dispositions do not match summary counts")
    return integrity, accepted_indices, verifications, counts


def _validate_stage_topology(state: Mapping[str, Any]) -> None:
    status = state.get("status")
    if status not in {"COMPLETED_WIN", "COMPLETED_NO_WIN"}:
        return
    stages = state.get("stages")
    if not isinstance(stages, dict) or set(stages) != set(_STAGE_ORDER):
        _fail(
            "STATE_INVALID",
            "pipeline state must contain exactly the five configured stages",
        )

    expected_machines = {
        "stage1_search": {"COMPLETED"},
        "stage2_sector_audit": {"COMPLETED"},
        "stage3_direction_audit": {"COMPLETED", "SKIPPED"},
        _STAGE4: {"COMPLETED"},
        _STAGE5: ({"COMPLETED"} if status == "COMPLETED_WIN" else {"SKIPPED"}),
    }
    for ordinal, stage_name in enumerate(_STAGE_ORDER, start=1):
        record = stages[stage_name]
        if not isinstance(record, dict):
            _fail("STATE_INVALID", f"{stage_name} stage record is malformed")
        machine_status = record.get("machine_status")
        attempt = record.get("attempt")
        command = record.get("command")
        command_sha256 = record.get("command_sha256")
        stage_ordinal = record.get("ordinal")
        exit_code = record.get("exit_code")
        if (
            isinstance(record.get("ordinal"), bool)
            or not isinstance(stage_ordinal, int)
            or record.get("ordinal") != ordinal
            or machine_status not in expected_machines[stage_name]
            or record.get("status") != machine_status
            or record.get("exit_code") != 0
            or isinstance(exit_code, bool)
            or not isinstance(exit_code, int)
            or isinstance(attempt, bool)
            or not isinstance(attempt, int)
            or attempt <= 0
            or not _is_lower_sha256(record.get("stage_fingerprint"))
            or not isinstance(command, list)
            or not command
            or any(not isinstance(item, str) for item in command)
            or not _is_lower_sha256(command_sha256)
            or command_sha256 != _pipeline_fingerprint(command)
        ):
            _fail(
                "STATE_INVALID",
                f"{stage_name} is not a valid terminal stage record",
            )


def _validate_state_identity(
    *,
    state: Mapping[str, Any],
    repo: Path,
    run_id: str,
    pipeline_root: Path,
) -> str:
    _require_schema_one(state, label="pipeline state")
    if state.get("gate") != "qcode-humanize-five-stage-pipeline":
        _fail("STATE_INVALID", "unexpected pipeline state gate")
    if state.get("run_id") != run_id:
        _fail("STATE_INVALID", "pipeline state run_id mismatch")
    expected_root = repo / "results" / "humanize" / "pipelines" / run_id
    if pipeline_root != expected_root:
        _fail("UNSAFE_PATH", "pipeline root is not the fixed repository run path")
    if state.get("active_stage") is not None or state.get("failure") is not None:
        _fail("STATE_INVALID", "completed pipeline still has active/failure state")
    completed_at = state.get("completed_at")
    if not isinstance(completed_at, str) or not completed_at:
        _fail("STATE_INVALID", "completed pipeline has no stable completed_at")
    config = state.get("config")
    pinned_artifact = repo / "results" / "known_answer_gate.json"
    pinned_trust = repo / "results" / "known_answer_trust.json"
    if (
        not isinstance(config, dict)
        or config.get("repo_dir") != str(repo)
        or config.get("run_id") != run_id
        or config.get("known_answer_artifact") != str(pinned_artifact)
        or config.get("known_answer_trust") != str(pinned_trust)
    ):
        _fail(
            "STATE_INVALID",
            "pipeline configuration is not bound to repository-pinned evidence",
        )
    config_fingerprint = state.get("config_fingerprint")
    if not _is_lower_sha256(
        config_fingerprint
    ) or config_fingerprint != _pipeline_fingerprint(config):
        _fail(
            "STATE_INVALID",
            "pipeline config_fingerprint does not match its configuration",
        )
    _validate_stage_topology(state)
    return completed_at


def _validate_state(
    *,
    state: Mapping[str, Any],
    repo: Path,
    run_id: str,
    pipeline_root: Path,
    stage4_summary_path: Path,
    stage5_path: Path,
    certificate_count: int,
) -> str:
    _require_schema_one(state, label="pipeline state")
    if state.get("gate") != "qcode-humanize-five-stage-pipeline":
        _fail("STATE_INVALID", "unexpected pipeline state gate")
    if state.get("run_id") != run_id:
        _fail("STATE_INVALID", "pipeline state run_id mismatch")
    status = state.get("status")
    if status == "COMPLETED_NO_WIN":
        raise ReleaseNotExportableError(
            "NO_CERTIFIED_WIN",
            f"pipeline {run_id} completed without a certified win",
        )
    if status != "COMPLETED_WIN":
        _fail(
            "PIPELINE_NOT_COMPLETE", f"pipeline status is {status!r}, not COMPLETED_WIN"
        )
    if state.get("active_stage") is not None or state.get("failure") is not None:
        _fail("STATE_INVALID", "completed pipeline still has active/failure state")
    completed_at = state.get("completed_at")
    if not isinstance(completed_at, str) or not completed_at:
        _fail("STATE_INVALID", "completed pipeline has no stable completed_at")

    config = state.get("config")
    pinned_artifact = repo / "results" / "known_answer_gate.json"
    pinned_trust = repo / "results" / "known_answer_trust.json"
    if (
        not isinstance(config, dict)
        or config.get("repo_dir") != str(repo)
        or config.get("run_id") != run_id
        or config.get("known_answer_artifact") != str(pinned_artifact)
        or config.get("known_answer_trust") != str(pinned_trust)
    ):
        _fail(
            "STATE_INVALID",
            "pipeline configuration is not bound to this repository's pinned evidence",
        )
    result = state.get("result")
    verified_certificates = (
        result.get("verified_certificates") if isinstance(result, dict) else None
    )
    if (
        not isinstance(result, dict)
        or isinstance(verified_certificates, bool)
        or not isinstance(verified_certificates, int)
        or verified_certificates != certificate_count
        or result.get("stage4_summary") != str(stage4_summary_path)
        or result.get("strict_gate") != str(stage5_path)
    ):
        _fail("STATE_INVALID", "pipeline result does not name the exported evidence")
    expected_root = repo / "results" / "humanize" / "pipelines" / run_id
    if pipeline_root != expected_root:
        _fail("UNSAFE_PATH", "pipeline root is not the fixed repository run path")
    return completed_at


@contextmanager
def _pipeline_lock(pipeline_root: Path) -> Iterable[None]:
    lock_path = pipeline_root / "pipeline.lock"
    _reject_symlink_components(lock_path, root=pipeline_root, include_leaf=False)
    flags = os.O_RDWR | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(lock_path, flags, 0o600)
    except OSError as exc:
        _fail("UNSAFE_LOCK", f"cannot safely open pipeline lock {lock_path}: {exc}")
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            _fail("UNSAFE_LOCK", f"pipeline lock is not a regular file: {lock_path}")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            _fail("PIPELINE_BUSY", f"pipeline {pipeline_root.name} is still locked")
        try:
            yield
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
    finally:
        os.close(descriptor)


def _json_bytes(value: Any) -> bytes:
    try:
        return (
            json.dumps(
                value,
                sort_keys=True,
                ensure_ascii=False,
                allow_nan=False,
                indent=2,
            )
            + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        _fail("SOURCE_INVALID", f"release JSON cannot be serialized: {exc}")


def _write_new_file(path: Path, content: bytes) -> None:
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_EXCL
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    descriptor = os.open(path, flags, 0o600)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            descriptor = -1
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _result(
    *,
    status: str,
    run_id: str,
    manifest_path: Path,
    manifest: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "status": status,
        "run_id": run_id,
        "manifest": str(manifest_path),
        "manifest_sha256": manifest["manifest_sha256"],
        "certificates": len(manifest["certificates"]),
    }


def _check_existing_export(
    *,
    destination: Path,
    manifest: Mapping[str, Any],
    certificates: list[dict[str, Any]],
    repo: Path,
    trust_path: Path,
    run_id: str,
) -> dict[str, Any]:
    _require_directory(destination, root=repo, label="release destination")
    expected_top = {"challenge_manifest.json", "certificates"}
    try:
        actual_top = {item.name for item in os.scandir(destination)}
    except OSError as exc:
        _fail("DESTINATION_CONFLICT", f"cannot inspect release destination: {exc}")
    if not expected_top.issubset(actual_top):
        _fail(
            "DESTINATION_CONFLICT",
            f"existing release destination is not the same snapshot: {destination}",
        )
    manifest_path = destination / "challenge_manifest.json"
    _existing, existing_raw = _read_json_object(
        manifest_path,
        root=destination,
        label="existing release manifest",
    )
    if existing_raw != _json_bytes(manifest):
        _fail(
            "DESTINATION_CONFLICT",
            f"existing challenge manifest differs: {manifest_path}",
        )
    certificate_dir = destination / "certificates"
    _require_directory(
        certificate_dir,
        root=destination,
        label="existing release certificates",
    )
    expected_names = {
        f"{certificate['certificate_sha256']}.json" for certificate in certificates
    }
    try:
        actual_names = {item.name for item in os.scandir(certificate_dir)}
    except OSError as exc:
        _fail("DESTINATION_CONFLICT", f"cannot inspect release certificates: {exc}")
    if actual_names != expected_names:
        _fail(
            "DESTINATION_CONFLICT",
            "existing release certificate files differ",
        )
    for certificate in certificates:
        certificate_path = certificate_dir / (
            f"{certificate['certificate_sha256']}.json"
        )
        _existing_certificate, existing_raw = _read_json_object(
            certificate_path,
            root=certificate_dir,
            label="existing release certificate",
        )
        if existing_raw != _json_bytes(certificate):
            _fail(
                "DESTINATION_CONFLICT",
                f"existing release certificate differs: {certificate_path}",
            )
    validation = validate_release_manifest(
        manifest_path,
        known_answer_trust_path=trust_path,
        expected_run_id=run_id,
    )
    if validation.get("passed") is not True:
        _fail(
            "DESTINATION_CONFLICT",
            "existing release snapshot fails validation: "
            + "; ".join(validation.get("failures") or []),
        )
    return _result(
        status="already-exported",
        run_id=run_id,
        manifest_path=manifest_path,
        manifest=manifest,
    )


def _rename_noreplace(source: Path, destination: Path) -> bool:
    """Atomically publish without ever replacing an existing path."""
    source_parent = source.parent
    destination_parent = destination.parent
    source_directory_fd = -1
    destination_directory_fd = -1
    flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    try:
        source_expected = source_parent.lstat()
        source_directory_fd = os.open(source_parent, flags)
        destination_expected = destination_parent.lstat()
        destination_directory_fd = os.open(destination_parent, flags)
    except OSError as exc:
        if source_directory_fd >= 0:
            os.close(source_directory_fd)
        if destination_directory_fd >= 0:
            os.close(destination_directory_fd)
        _fail("UNSAFE_PATH", f"cannot open release directory safely: {exc}")
    if _inode_identity(os.fstat(source_directory_fd)) != _inode_identity(
        source_expected
    ) or _inode_identity(os.fstat(destination_directory_fd)) != _inode_identity(
        destination_expected
    ):
        os.close(source_directory_fd)
        os.close(destination_directory_fd)
        _fail("UNSAFE_PATH", "release directory changed while opening it")

    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        os.close(source_directory_fd)
        os.close(destination_directory_fd)
        _fail(
            "ATOMIC_NOREPLACE_UNAVAILABLE",
            "renameat2 is required for immutable release publication",
        )
    renameat2.argtypes = [
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    try:
        result = renameat2(
            source_directory_fd,
            os.fsencode(source.name),
            destination_directory_fd,
            os.fsencode(destination.name),
            1,
        )
    finally:
        os.close(source_directory_fd)
        os.close(destination_directory_fd)
    if result == 0:
        return True
    failure_errno = ctypes.get_errno()
    if failure_errno in {errno.EEXIST, errno.ENOTEMPTY}:
        return False
    if failure_errno in {errno.ENOSYS, errno.EINVAL}:
        _fail(
            "ATOMIC_NOREPLACE_UNAVAILABLE",
            "kernel does not support atomic no-replace publication",
        )
    _fail(
        "DESTINATION_CONFLICT",
        f"atomic release publication failed: {os.strerror(failure_errno)}",
    )


def _inode_identity(metadata: os.stat_result) -> tuple[int, int]:
    return metadata.st_dev, metadata.st_ino


def _safe_cleanup_staging(
    *,
    temporary: Path,
    runs_root: Path,
    certificates: list[dict[str, Any]],
    temporary_identity: tuple[int, int],
    certificate_identity: tuple[int, int] | None,
) -> None:
    runs_fd = -1
    temporary_fd = -1
    certificate_fd = -1
    flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    try:
        runs_fd = os.open(runs_root, flags)
        temporary_fd = os.open(
            temporary.name,
            flags,
            dir_fd=runs_fd,
        )
        if _inode_identity(os.fstat(temporary_fd)) != temporary_identity:
            return
        if certificate_identity is not None:
            try:
                certificate_fd = os.open("certificates", flags, dir_fd=temporary_fd)
            except OSError:
                certificate_fd = -1
            if (
                certificate_fd >= 0
                and _inode_identity(os.fstat(certificate_fd)) == certificate_identity
            ):
                for certificate in certificates:
                    name = f"{certificate['certificate_sha256']}.json"
                    try:
                        os.unlink(name, dir_fd=certificate_fd)
                    except OSError:
                        pass
                os.close(certificate_fd)
                certificate_fd = -1
                try:
                    current = os.stat(
                        "certificates",
                        dir_fd=temporary_fd,
                        follow_symlinks=False,
                    )
                    if _inode_identity(current) == certificate_identity:
                        os.rmdir("certificates", dir_fd=temporary_fd)
                except OSError:
                    pass
        try:
            os.unlink("challenge_manifest.json", dir_fd=temporary_fd)
        except OSError:
            pass
        try:
            current = os.stat(temporary.name, dir_fd=runs_fd, follow_symlinks=False)
            if _inode_identity(current) == temporary_identity:
                os.close(temporary_fd)
                temporary_fd = -1
                os.rmdir(temporary.name, dir_fd=runs_fd)
        except OSError:
            pass
    except OSError:
        pass
    finally:
        for descriptor in (certificate_fd, temporary_fd, runs_fd):
            if descriptor >= 0:
                os.close(descriptor)


def _check_existing_certificate_set(
    *,
    destination: Path,
    certificates: list[dict[str, Any]],
) -> None:
    certificate_dir = destination / "certificates"
    _require_directory(
        certificate_dir,
        root=destination,
        label="existing release certificates",
    )
    expected_names = {
        f"{certificate['certificate_sha256']}.json" for certificate in certificates
    }
    try:
        actual_names = {item.name for item in os.scandir(certificate_dir)}
    except OSError as exc:
        _fail("DESTINATION_CONFLICT", f"cannot inspect release certificates: {exc}")
    if actual_names != expected_names:
        _fail(
            "DESTINATION_CONFLICT",
            "existing release certificate files differ",
        )
    for certificate in certificates:
        certificate_path = certificate_dir / (
            f"{certificate['certificate_sha256']}.json"
        )
        _existing_certificate, existing_raw = _read_json_object(
            certificate_path,
            root=certificate_dir,
            label="existing release certificate",
        )
        if existing_raw != _json_bytes(certificate):
            _fail(
                "DESTINATION_CONFLICT",
                f"existing release certificate differs: {certificate_path}",
            )


def _publish_staged_into_existing(
    *,
    temporary: Path,
    destination: Path,
    manifest: dict[str, Any],
    certificates: list[dict[str, Any]],
    repo: Path,
    trust_path: Path,
    run_id: str,
) -> dict[str, Any]:
    _require_directory(destination, root=repo, label="release destination")
    manifest_path = destination / "challenge_manifest.json"
    if manifest_path.exists():
        return _check_existing_export(
            destination=destination,
            manifest=manifest,
            certificates=certificates,
            repo=repo,
            trust_path=trust_path,
            run_id=run_id,
        )

    staged_certificates = temporary / "certificates"
    final_certificates = destination / "certificates"
    if final_certificates.exists() or not _rename_noreplace(
        staged_certificates, final_certificates
    ):
        _check_existing_certificate_set(
            destination=destination,
            certificates=certificates,
        )
    else:
        _fsync_directory(destination)

    staged_manifest = temporary / "challenge_manifest.json"
    if not _rename_noreplace(staged_manifest, manifest_path):
        return _check_existing_export(
            destination=destination,
            manifest=manifest,
            certificates=certificates,
            repo=repo,
            trust_path=trust_path,
            run_id=run_id,
        )
    _fsync_directory(destination)
    return _result(
        status="exported",
        run_id=run_id,
        manifest_path=manifest_path,
        manifest=manifest,
    )


def _publish_snapshot(
    *,
    runs_root: Path,
    destination: Path,
    manifest: dict[str, Any],
    certificates: list[dict[str, Any]],
    repo: Path,
    trust_path: Path,
    run_id: str,
) -> dict[str, Any]:
    temporary = Path(tempfile.mkdtemp(prefix=f".{run_id}.release-", dir=runs_root))
    temporary_identity = _inode_identity(temporary.lstat())
    certificate_identity: tuple[int, int] | None = None
    published = False
    try:
        certificate_dir = temporary / "certificates"
        certificate_dir.mkdir(mode=0o700)
        certificate_identity = _inode_identity(certificate_dir.lstat())
        for certificate in certificates:
            certificate_path = certificate_dir / (
                f"{certificate['certificate_sha256']}.json"
            )
            _write_new_file(certificate_path, _json_bytes(certificate))
        _fsync_directory(certificate_dir)

        # The manifest is the publication marker and is deliberately written last.
        manifest_path = temporary / "challenge_manifest.json"
        _write_new_file(manifest_path, _json_bytes(manifest))
        _fsync_directory(temporary)
        validation = validate_release_manifest(
            manifest_path,
            known_answer_trust_path=trust_path,
            expected_run_id=run_id,
        )
        if validation.get("passed") is not True:
            _fail(
                "EXPORT_VALIDATION_FAILED",
                "staged release snapshot is invalid: "
                + "; ".join(validation.get("failures") or []),
            )
        if not _rename_noreplace(temporary, destination):
            return _publish_staged_into_existing(
                temporary=temporary,
                destination=destination,
                manifest=manifest,
                certificates=certificates,
                repo=repo,
                trust_path=trust_path,
                run_id=run_id,
            )
        published = True
        _fsync_directory(runs_root)
        final_manifest = destination / "challenge_manifest.json"
        return _result(
            status="exported",
            run_id=run_id,
            manifest_path=final_manifest,
            manifest=manifest,
        )
    finally:
        if not published:
            _safe_cleanup_staging(
                temporary=temporary,
                runs_root=runs_root,
                certificates=certificates,
                temporary_identity=temporary_identity,
                certificate_identity=certificate_identity,
            )


def export_release(
    *,
    repo_dir: Path,
    run_id: str,
    python_executable: str = sys.executable,
) -> dict[str, Any]:
    """Export one completed five-stage win into the formal release layout.

    The source and destination are intentionally fixed beneath ``repo_dir``.
    This function has no override for trust, the pipeline root, or the release
    root: all three are part of the production trust boundary.
    """

    run_id = _safe_run_id(run_id)
    try:
        repo = Path(repo_dir).resolve(strict=True)
    except OSError as exc:
        _fail("UNSAFE_PATH", f"repository is unavailable: {repo_dir}: {exc}")
    try:
        metadata = repo.lstat()
    except OSError as exc:
        _fail("UNSAFE_PATH", f"cannot inspect repository {repo}: {exc}")
    if not stat.S_ISDIR(metadata.st_mode):
        _fail("UNSAFE_PATH", f"repository is not a directory: {repo}")

    pipeline_root = repo / "results" / "humanize" / "pipelines" / run_id
    _require_directory(pipeline_root, root=repo, label="pipeline run")
    with _pipeline_lock(pipeline_root):
        state_path = pipeline_root / "state.json"
        stage4_certificates_path = (
            pipeline_root / "artifacts" / "stage4-certificates.jsonl"
        )
        stage4_summary_path = pipeline_root / "artifacts" / "stage4-summary.json"
        stage5_path = pipeline_root / "artifacts" / "stage5-final-gate.json"
        trust_path = repo / "results" / "known_answer_trust.json"
        known_answer_path = repo / "results" / "known_answer_gate.json"
        known_code_registry_path = repo / "results" / "known_code_registry.json"
        finalizer_path = repo / "scripts" / "finalize_challenge.py"
        strict_runner_path = repo / "tests" / "verify_known_answer_gate.py"
        controller_source_path = repo / "humanize" / "pipeline.py"
        evaluation_source_root = repo / "evaluation"
        strict_verifier_paths = tuple(
            repo / "scripts" / name
            for name in _STRICT_VERIFIER_SCRIPT_NAMES
        )

        state, state_raw = _read_json_object(
            state_path,
            root=pipeline_root,
            label="pipeline state",
        )
        # Recognize the valid no-win terminal state before demanding win artifacts.
        _validate_state_identity(
            state=state,
            repo=repo,
            run_id=run_id,
            pipeline_root=pipeline_root,
        )
        if state.get("status") == "COMPLETED_NO_WIN":
            raise ReleaseNotExportableError(
                "NO_CERTIFIED_WIN",
                f"pipeline {run_id} completed without a certified win",
            )
        certificates, stage4_certificates_raw = _read_jsonl_objects(
            stage4_certificates_path,
            root=pipeline_root,
            label="Stage 4 certificates",
        )
        stage4_summary, stage4_summary_raw = _read_json_object(
            stage4_summary_path,
            root=pipeline_root,
            label="Stage 4 summary",
        )
        stage5, stage5_raw = _read_json_object(
            stage5_path,
            root=pipeline_root,
            label="Stage 5 final gate",
        )
        trust, trust_raw = _read_json_object(
            trust_path,
            root=repo,
            label="repository known-answer trust",
        )
        known_answer_raw = _read_regular_bytes(
            known_answer_path,
            root=repo,
            label="repository known-answer artifact",
        )
        strict_source_fingerprint, strict_source_files = _source_fingerprint(
            repo,
            controller_source_path,
            evaluation_source_root,
            finalizer_path,
            *strict_verifier_paths,
            strict_runner_path,
            known_code_registry_path,
        )
        finalizer_raw = strict_source_files[finalizer_path]
        strict_runner_raw = strict_source_files[strict_runner_path]
        known_code_registry_raw = strict_source_files[known_code_registry_path]
        controller_source_raw = strict_source_files[controller_source_path]
        strict_verifier_raw = {
            path: strict_source_files[path]
            for path in strict_verifier_paths
        }
        known_answer_sha = _sha256_bytes(known_answer_raw)
        config = state.get("config")
        if not isinstance(config, Mapping):
            _fail("STATE_INVALID", "pipeline state config must be an object")
        configured_python = config.get("python_executable")
        if not isinstance(configured_python, str) or not configured_python:
            _fail("STATE_INVALID", "pipeline config python_executable is invalid")
        try:
            authorized_invocation, _authorized_realpath = (
                resolve_python_executable(
                    python_executable,
                    cwd=repo,
                )
            )
            configured_invocation, _configured_realpath = (
                resolve_python_executable(
                    configured_python,
                    cwd=repo,
                )
            )
            if configured_invocation != authorized_invocation:
                _fail(
                    "RUNTIME_INVALID",
                    "pipeline worker interpreter is not the explicitly "
                    "authorized release interpreter",
                )
            current_runtime_provenance = probe_python_runtime(
                python_executable,
                cwd=repo,
            )
        except RuntimeProbeError as exc:
            _fail(
                "RUNTIME_INVALID",
                f"cannot identify configured proof interpreter: {exc}",
            )
        current_proof_runtime = current_runtime_provenance.get("runtime")
        current_proof_interpreter = current_runtime_provenance.get("interpreter")
        if not isinstance(current_proof_runtime, Mapping) or not isinstance(
            current_proof_interpreter, Mapping
        ):
            _fail(
                "RUNTIME_INVALID",
                "configured proof interpreter returned malformed provenance",
            )
        try:
            current_proof_runtime = validate_proof_runtime_fingerprint(
                current_proof_runtime,
            )
        except ValueError as exc:
            _fail(
                "RUNTIME_INVALID",
                f"configured proof runtime is malformed: {exc}",
            )
        if current_proof_runtime["interpreter"] != dict(
            current_proof_interpreter
        ):
            _fail(
                "RUNTIME_INVALID",
                "configured proof runtime has conflicting interpreter identity",
            )
        current_proof_interpreter = current_proof_runtime["interpreter"]
        _validate_trust(
            trust,
            artifact_sha256=known_answer_sha,
            proof_runtime=current_proof_runtime,
        )

        stages = state.get("stages")
        if not isinstance(stages, dict):
            _fail("STATE_INVALID", "pipeline state has no stages object")
        stage4_record = _require_exact_output_hashes(
            stages.get(_STAGE4),
            {
                stage4_certificates_path: stage4_certificates_raw,
                stage4_summary_path: stage4_summary_raw,
            },
            stage=_STAGE4,
        )
        stage5_record = _require_exact_output_hashes(
            stages.get(_STAGE5),
            {stage5_path: stage5_raw},
            stage=_STAGE5,
        )
        _require_exact_input_hashes(
            stage5_record,
            {
                stage4_certificates_path: stage4_certificates_raw,
                finalizer_path: finalizer_raw,
                **strict_verifier_raw,
                known_answer_path: known_answer_raw,
                known_code_registry_path: known_code_registry_raw,
                strict_runner_path: strict_runner_raw,
                trust_path: trust_raw,
            },
        )

        completed_at = _validate_state(
            state=state,
            repo=repo,
            run_id=run_id,
            pipeline_root=pipeline_root,
            stage4_summary_path=stage4_summary_path,
            stage5_path=stage5_path,
            certificate_count=len(certificates),
        )
        config = state["config"]
        stage5_current_provenance = _validate_current_stage5_provenance(
            record=stage5_record,
            config=config,
            repo=repo,
            pipeline_root=pipeline_root,
            stage4_certificates_path=stage4_certificates_path,
            stage5_path=stage5_path,
            controller_source_sha256=_sha256_bytes(controller_source_raw),
            source_fingerprint=strict_source_fingerprint,
            known_code_registry_sha256=_sha256_bytes(known_code_registry_raw),
            strict_runner_sha256=_sha256_bytes(strict_runner_raw),
            proof_runtime=current_proof_runtime,
            proof_interpreter=current_proof_interpreter,
        )
        certificate_hashes = _validate_stage4(
            summary=stage4_summary,
            certificates=certificates,
            certificates_path=stage4_certificates_path,
            pipeline_root=pipeline_root,
            known_answer_sha256=known_answer_sha,
        )
        (
            integrity,
            accepted_indices,
            verifications,
            stage5_counts,
        ) = _validate_stage5(
            gate=stage5,
            certificates=certificates,
            certificate_hashes=certificate_hashes,
            trust=trust,
        )
        accepted_certificates = [
            certificates[index] for index in accepted_indices
        ]
        accepted_hashes = [
            certificate_hashes[index] for index in accepted_indices
        ]
        config_fingerprint = state.get("config_fingerprint")
        if not _is_lower_sha256(config_fingerprint):
            _fail("STATE_INVALID", "pipeline config_fingerprint is invalid")
        stage_provenance: dict[str, dict[str, Any]] = {}
        for stage_name, record in (
            (
                _STAGE4,
                stage4_record,
            ),
            (
                _STAGE5,
                stage5_record,
            ),
        ):
            attempt = record.get("attempt")
            fingerprint = record.get("stage_fingerprint")
            if (
                isinstance(attempt, bool)
                or not isinstance(attempt, int)
                or attempt <= 0
                or not _is_lower_sha256(fingerprint)
            ):
                _fail(
                    "STATE_INVALID",
                    f"{stage_name} execution provenance is invalid",
                )
            stage_provenance[stage_name] = {
                "attempt": attempt,
                "stage_fingerprint": fingerprint,
            }

        all_stage_provenance = {
            stage_name: {
                "ordinal": record["ordinal"],
                "status": record["status"],
                "machine_status": record["machine_status"],
                "attempt": record["attempt"],
                "stage_fingerprint": record["stage_fingerprint"],
                "command_sha256": record["command_sha256"],
            }
            for stage_name, record in ((name, stages[name]) for name in _STAGE_ORDER)
        }
        entries = [
            {
                "file": f"certificates/{certificate_sha}.json",
                "certificate_sha256": certificate_sha,
                "verification": verification,
            }
            for certificate_sha, verification in zip(
                accepted_hashes,
                verifications,
                strict=True,
            )
        ]
        stage5_artifact_sha256 = _sha256_bytes(stage5_raw)
        manifest: dict[str, Any] = {
            "schema_version": 1,
            "gate": "qldpc-challenge-release",
            "run_id": run_id,
            "generated_at": completed_at,
            "passed": True,
            "known_answer_integrity": integrity,
            "source_evaluations": len(certificates),
            "source_total": stage5_counts["total"],
            "accepted": stage5_counts["accepted"],
            "rejected": stage5_counts["rejected"],
            "incomplete": stage5_counts["incomplete"],
            "stage5_artifact_sha256": stage5_artifact_sha256,
            "source_pipeline": {
                "schema_version": 1,
                "gate": "qcode-humanize-five-stage-pipeline",
                "state_sha256": _sha256_bytes(state_raw),
                "config_fingerprint": config_fingerprint,
                "stages": all_stage_provenance,
                "stage4": {
                    **stage_provenance[_STAGE4],
                    "summary_sha256": _sha256_bytes(stage4_summary_raw),
                    "certificates_sha256": _sha256_bytes(stage4_certificates_raw),
                },
                "stage5": {
                    **stage_provenance[_STAGE5],
                    "final_gate_sha256": stage5_artifact_sha256,
                    "finalizer_sha256": _sha256_bytes(finalizer_raw),
                    **stage5_current_provenance,
                },
            },
            "eligible_candidates": len(accepted_certificates),
            "certificates": entries,
        }
        manifest["manifest_sha256"] = canonical_sha256(
            manifest,
            omit="manifest_sha256",
        )

        results_root = repo / "results"
        _require_directory(results_root, root=repo, label="results")
        runs_root = results_root / "runs"
        _reject_symlink_components(runs_root, root=repo)
        try:
            runs_root.mkdir(mode=0o700, exist_ok=True)
        except OSError as exc:
            _fail("UNSAFE_PATH", f"cannot create release root {runs_root}: {exc}")
        _require_directory(runs_root, root=repo, label="release root")
        destination = runs_root / run_id
        _reject_symlink_components(destination, root=repo)
        return _publish_snapshot(
            runs_root=runs_root,
            destination=destination,
            manifest=manifest,
            certificates=accepted_certificates,
            repo=repo,
            trust_path=trust_path,
            run_id=run_id,
        )


__all__ = [
    "ReleaseExportError",
    "ReleaseNotExportableError",
    "export_release",
]
