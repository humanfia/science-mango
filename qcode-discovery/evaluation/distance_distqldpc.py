"""Pinned DistQLDPC lower-bound decisions for CSS distance proofs.

DistQLDPC is an external MaxCDCL-based optimizer.  Its final ``c d : N`` line
is a complete distance decision, while progress bounds and ``o N`` alone are
not terminal proof evidence.  This adapter therefore fails closed on timeout,
non-zero exit, malformed output, binary replacement, or surviving children.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from evaluation.css_logical_detector import verify_css_logical_detectors
from evaluation.distqldpc_supervisor import SUPERVISOR_PROTOCOL

DISTQLDPC_EVIDENCE_KIND = "qcode-css-distqldpc-distance-evidence"
DISTQLDPC_EVIDENCE_SCHEMA_VERSION = 1
DISTQLDPC_FORMULATION = "css-full-distance-distqldpc-maxcdcl-v1"
DISTQLDPC_REPOSITORY = "https://github.com/guluchen/DistQLDPC"
DISTQLDPC_PINNED_COMMIT = "c01fa93eb5e1e62948e4861e2c164a6b64fe88eb"
DISTQLDPC_PINNED_BINARY_SHA256 = (
    "9e09c544d5151d872dc1037dcb1440509e27b8b485a7f9ea5a15d6e55b36d3fa"
)
DEFAULT_DISTQLDPC_EXE = Path(
    "/root/vendor/DistQLDPC-c01fa93/bin/distqldpc"
)
DISTQLDPC_EXECUTION_POLICY = "distqldpc-supervised-private-pg-hard-wall-v2"
DISTQLDPC_SUPERVISOR_PYTHON_FLAGS = ("-I", "-B")
_DISTQLDPC_SUPERVISOR_PATH = Path(__file__).with_name(
    "distqldpc_supervisor.py"
)
DISTQLDPC_TERMINAL_OUTCOMES = frozenset({"exact"})
DISTQLDPC_RETRYABLE_OUTCOMES = frozenset({
    "backend_unavailable",
    "cancelled",
    "hard_timeout",
    "solver_error",
})
DISTQLDPC_CARDINALITY_MODES = (
    "default",
    "no-card",
    "sinz",
    "mto",
    "both-force",
)
_DISTQLDPC_CARDINALITY_FLAGS = {
    "default": (),
    "no-card": ("-no-card",),
    "sinz": ("-card-sinz",),
    "mto": ("-card-mto",),
    "both-force": ("-card-both-force",),
}

_MAX_CAPTURE_BYTES = 16 * 1024 * 1024
_TERMINATION_TERM_PHASE_MAX_S = 1.0
_RE_D_LB = re.compile(r"^c\s+d_lb:\s*(\d+)\s*$", re.MULTILINE)
_RE_D_UB = re.compile(r"^c\s+d_ub:\s*(\d+)\s*$", re.MULTILINE)
_RE_D = re.compile(r"^c\s+d\s*:\s*(\d+)\s*$", re.MULTILINE)
_RE_D_UNKNOWN = re.compile(r"^c\s+d\s*:\s*UNKNOWN\s*$", re.MULTILINE)
_RE_O = re.compile(r"^o\s+(-?\d+)\s*$", re.MULTILINE)
_RE_TIMEOUT = re.compile(r"^c\s+status:\s*TIMEOUT\b", re.MULTILINE)


class DistQLDPCBackendUnavailable(RuntimeError):
    """Raised when the pinned external backend cannot be admitted."""


def distqldpc_cardinality_flags(mode: str) -> tuple[str, ...]:
    """Return the pinned CLI flag tuple for one supported search mode."""

    if not isinstance(mode, str) or mode not in _DISTQLDPC_CARDINALITY_FLAGS:
        raise ValueError("unsupported DistQLDPC cardinality mode")
    return _DISTQLDPC_CARDINALITY_FLAGS[mode]


def _canonical_json(value: Any) -> Any:
    try:
        encoded = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise ValueError("DistQLDPC identity must be strict JSON data") from exc
    return json.loads(encoded)


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _runtime_source_identity() -> dict[str, Any]:
    adapter_path = Path(__file__).resolve(strict=True)
    supervisor_path = _DISTQLDPC_SUPERVISOR_PATH.resolve(strict=True)
    identity = {
        "protocol": SUPERVISOR_PROTOCOL,
        "adapter": {
            "module": "evaluation.distance_distqldpc",
            "sha256": _file_sha256(adapter_path),
        },
        "supervisor": {
            "module": "evaluation.distqldpc_supervisor",
            "sha256": _file_sha256(supervisor_path),
        },
    }
    identity["identity_sha256"] = _canonical_sha256(identity)
    return identity


def _array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode())
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _matrix_text(value: np.ndarray) -> bytes:
    rows = [" ".join(str(int(bit)) for bit in row) for row in value.tolist()]
    return (("\n".join(rows) + "\n") if rows else "").encode("ascii")


def _binary_matrix(name: str, value: np.ndarray) -> np.ndarray:
    raw = np.asarray(value)
    if raw.ndim != 2:
        raise ValueError(f"{name} must be a two-dimensional matrix")
    try:
        binary = np.asarray(raw, dtype=np.uint8)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(f"{name} must contain binary integers") from exc
    if not np.array_equal(raw, binary) or np.any(binary > 1):
        raise ValueError(f"{name} must contain only 0/1 entries")
    return np.ascontiguousarray(binary)


def _logical_detector_report(
    matrices: Mapping[str, np.ndarray],
) -> dict[str, Any]:
    report = verify_css_logical_detectors(
        matrices["Hx"],
        matrices["Hz"],
        matrices["Gz"],
        matrices["Gx"],
    )
    if report.get("verified") is not True:
        raise ValueError("CSS logical detector completeness replay failed")
    return report


def distqldpc_matrix_bundle(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> dict[str, np.ndarray]:
    """Validate CSS matrices and map qcode logical labels to DistQLDPC files."""

    matrices = {
        "Hx": _binary_matrix("hx", hx),
        "Hz": _binary_matrix("hz", hz),
        # DistQLDPC Gx is a Z representative in ker(Hx)/row(Hz).
        "Gx": _binary_matrix("lz", lz),
        # DistQLDPC Gz is an X representative in ker(Hz)/row(Hx).
        "Gz": _binary_matrix("lx", lx),
    }
    n = int(matrices["Hx"].shape[1])
    k = int(matrices["Gx"].shape[0])
    if n < 1 or k < 1:
        raise ValueError("DistQLDPC requires positive n and k")
    if any(matrix.shape[1] != n for matrix in matrices.values()):
        raise ValueError("DistQLDPC matrices must have a common column count")
    if matrices["Gz"].shape != (k, n):
        raise ValueError("DistQLDPC logical bases must have equal shape")
    if np.any((matrices["Hx"] @ matrices["Hz"].T) & 1):
        raise ValueError("CSS checks do not commute")
    if np.any((matrices["Hx"] @ matrices["Gx"].T) & 1):
        raise ValueError("DistQLDPC Gx is not in ker(Hx)")
    if np.any((matrices["Hz"] @ matrices["Gz"].T) & 1):
        raise ValueError("DistQLDPC Gz is not in ker(Hz)")
    if not np.array_equal(
        (matrices["Gz"] @ matrices["Gx"].T) & 1,
        np.eye(k, dtype=np.uint8),
    ):
        raise ValueError("DistQLDPC logical bases fail CSS duality")
    _logical_detector_report(matrices)
    return matrices


def _matrix_records(matrices: Mapping[str, np.ndarray]) -> dict[str, Any]:
    return {
        name: {
            "shape": list(matrix.shape),
            "array_sha256": _array_sha256(name, matrix),
            "text_sha256": hashlib.sha256(_matrix_text(matrix)).hexdigest(),
        }
        for name, matrix in matrices.items()
    }


def inspect_distqldpc_binary(
    binary: Path | str,
    *,
    expected_binary_sha256: str = DISTQLDPC_PINNED_BINARY_SHA256,
    source_commit: str = DISTQLDPC_PINNED_COMMIT,
) -> dict[str, Any]:
    """Resolve and hash the explicitly selected pinned executable."""

    requested = Path(binary).expanduser()
    try:
        resolved = requested.resolve(strict=True)
        metadata = resolved.stat()
    except OSError as exc:
        raise DistQLDPCBackendUnavailable(
            f"DistQLDPC binary is unavailable: {exc}"
        ) from exc
    if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved, os.X_OK):
        raise DistQLDPCBackendUnavailable(
            "DistQLDPC path is not an executable regular file"
        )
    actual_sha256 = _file_sha256(resolved)
    if actual_sha256 != expected_binary_sha256:
        raise DistQLDPCBackendUnavailable(
            "DistQLDPC binary SHA256 does not match the pinned official build"
        )
    identity = {
        "distribution": "DistQLDPC",
        "interface": "distqldpc-cli",
        "repository": DISTQLDPC_REPOSITORY,
        "source_commit": str(source_commit),
        "requested_path": str(requested.absolute()),
        "resolved_path": str(resolved),
        "file_size": int(metadata.st_size),
        "file_mode": stat.S_IMODE(metadata.st_mode),
        "binary_sha256": actual_sha256,
    }
    identity["identity_sha256"] = _canonical_sha256(identity)
    return identity


def parse_distqldpc_output(text: str) -> dict[str, Any]:
    """Parse progress and final lines without treating ``o`` as exact."""

    def values(pattern: re.Pattern[str]) -> list[int]:
        return [int(match.group(1)) for match in pattern.finditer(text)]

    lower_bounds = values(_RE_D_LB)
    upper_bounds = values(_RE_D_UB)
    exact_values = values(_RE_D)
    objectives = values(_RE_O)
    return {
        "d_lb": lower_bounds[-1] if lower_bounds else None,
        "d_ub": upper_bounds[-1] if upper_bounds else None,
        "d": exact_values[-1] if exact_values else None,
        "o": objectives[-1] if objectives else None,
        "d_lb_values": lower_bounds,
        "d_ub_values": upper_bounds,
        "d_values": exact_values,
        "o_values": objectives,
        "unknown_final": _RE_D_UNKNOWN.search(text) is not None,
        "reported_timeout": _RE_TIMEOUT.search(text) is not None,
    }


def _exact_output_failure(
    parsed: Mapping[str, Any], *, returncode: int, n: int
) -> str | None:
    if returncode != 0:
        return f"DistQLDPC exited with status {returncode}"
    if parsed.get("reported_timeout") is True or parsed.get("unknown_final") is True:
        return "DistQLDPC reported an incomplete timeout/UNKNOWN result"
    exact_values = parsed.get("d_values")
    objectives = parsed.get("o_values")
    if not isinstance(exact_values, list) or len(exact_values) != 1:
        return "DistQLDPC did not emit exactly one numeric final c d line"
    if not isinstance(objectives, list) or len(objectives) != 1:
        return "DistQLDPC did not emit exactly one final o line"
    distance = exact_values[0]
    if isinstance(distance, bool) or not isinstance(distance, int) or not 1 <= distance <= n:
        return "DistQLDPC final distance is outside [1,n]"
    if objectives[0] != distance:
        return "DistQLDPC c d and o lines disagree"
    if parsed.get("d_lb") != distance or parsed.get("d_ub") != distance:
        return "DistQLDPC final lower/upper bounds do not equal c d"
    return None


def _process_group_exists(process_group: int) -> bool:
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _terminate_process_group(
    process: subprocess.Popen[bytes],
    *,
    grace_s: float,
    absolute_deadline: float | None = None,
) -> dict[str, Any]:
    """Terminate and reap one private group within one total grace budget."""

    process_group = int(process.pid)
    relative_deadline = time.monotonic() + max(0.0, float(grace_s))
    if absolute_deadline is None:
        deadline = relative_deadline
    else:
        shared_deadline = float(absolute_deadline)
        if not math.isfinite(shared_deadline):
            raise ValueError("cleanup deadline must be finite")
        deadline = min(relative_deadline, shared_deadline)
    sent_term = False
    sent_kill = False
    try:
        os.killpg(process_group, signal.SIGTERM)
        sent_term = True
    except ProcessLookupError:
        pass
    now = time.monotonic()
    remaining = max(0.0, deadline - now)
    term_deadline = min(
        deadline,
        now + min(_TERMINATION_TERM_PHASE_MAX_S, remaining / 2.0),
    )
    try:
        process.wait(timeout=max(0.0, term_deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        pass
    if process.poll() is None or _process_group_exists(process_group):
        try:
            os.killpg(process_group, signal.SIGKILL)
            sent_kill = True
        except ProcessLookupError:
            pass
    if process.poll() is None:
        try:
            process.wait(timeout=max(0.0, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            pass
    while (
        _process_group_exists(process_group)
        and time.monotonic() < deadline
    ):
        time.sleep(min(0.01, max(0.0, deadline - time.monotonic())))
    return {
        "process_group": process_group,
        "sent_sigterm": sent_term,
        "sent_sigkill": sent_kill,
        "leader_reaped": process.poll() is not None,
        "group_survived": _process_group_exists(process_group),
        "cleanup_deadline_exhausted": time.monotonic() >= deadline,
    }


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{time.time_ns()}.tmp")
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(value, stream, indent=2, sort_keys=True, allow_nan=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        try:
            descriptor = os.open(path.parent, os.O_RDONLY)
        except OSError:
            return
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)


def _seal(result: dict[str, Any]) -> dict[str, Any]:
    unsigned = dict(result)
    unsigned.pop("evidence_sha256", None)
    result["evidence_sha256"] = _canonical_sha256(unsigned)
    return result


def _base_result(
    *,
    binding: Mapping[str, Any] | None,
    backend: Mapping[str, Any] | None,
    max_weight: int,
    hard_timeout_s: float,
) -> dict[str, Any]:
    return {
        "schema_version": DISTQLDPC_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": DISTQLDPC_EVIDENCE_KIND,
        "formulation": DISTQLDPC_FORMULATION,
        "instance": None if binding is None else dict(binding),
        "backend": None if backend is None else dict(backend),
        "max_weight": int(max_weight),
        "hard_timeout_s": float(hard_timeout_s),
        "operator": None,
        "objective": None,
        "exact_distance": None,
        "lower_bound": None,
        "upper_bound": None,
    }


def _instance_binding(
    matrices: Mapping[str, np.ndarray],
    *,
    max_weight: int,
    backend: Mapping[str, Any],
    cardinality_mode: str,
    checkpoint_identity: Mapping[str, Any] | str | None,
) -> dict[str, Any]:
    binding = {
        "formulation": DISTQLDPC_FORMULATION,
        "n": int(matrices["Hx"].shape[1]),
        "k": int(matrices["Gx"].shape[0]),
        "max_weight": int(max_weight),
        "matrix_files": _matrix_records(matrices),
        "logical_detector": _logical_detector_report(matrices),
        "backend": dict(backend),
        "solver_execution": {
            "policy": DISTQLDPC_EXECUTION_POLICY,
            "runtime_source": _runtime_source_identity(),
            "supervisor_python_argv": list(
                DISTQLDPC_SUPERVISOR_PYTHON_FLAGS
            ),
            "cardinality_mode": cardinality_mode,
            "cardinality_argv": list(
                distqldpc_cardinality_flags(cardinality_mode)
            ),
        },
        "checkpoint_identity": (
            None if checkpoint_identity is None else _canonical_json(checkpoint_identity)
        ),
    }
    binding["binding_sha256"] = _canonical_sha256(binding)
    return binding


def _verify_exact_evidence(
    evidence: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    max_weight: int,
    expected_cardinality_mode: str = "default",
    expected_checkpoint_identity: Mapping[str, Any] | str | None = None,
    expected_binary_sha256: str = DISTQLDPC_PINNED_BINARY_SHA256,
    expected_source_commit: str = DISTQLDPC_PINNED_COMMIT,
) -> list[str]:
    failures: list[str] = []
    expected_cardinality_argv = list(
        distqldpc_cardinality_flags(expected_cardinality_mode)
    )
    try:
        expected_runtime_source = _runtime_source_identity()
    except OSError as exc:
        expected_runtime_source = None
        failures.append(f"runtime source identity is unavailable: {exc}")
    try:
        matrices = distqldpc_matrix_bundle(hx, hz, lx, lz)
    except (TypeError, ValueError) as exc:
        return [f"matrix replay failed: {exc}"]
    backend = evidence.get("backend")
    instance = evidence.get("instance")
    if not isinstance(backend, Mapping):
        failures.append("backend identity is missing")
    else:
        backend_unsigned = dict(backend)
        identity_sha256 = backend_unsigned.pop("identity_sha256", None)
        if identity_sha256 != _canonical_sha256(backend_unsigned):
            failures.append("backend identity hash is invalid")
        if backend.get("distribution") != "DistQLDPC":
            failures.append("backend distribution is not DistQLDPC")
        if backend.get("repository") != DISTQLDPC_REPOSITORY:
            failures.append("backend repository is not pinned")
        if backend.get("source_commit") != expected_source_commit:
            failures.append("backend source commit is not pinned")
        if backend.get("binary_sha256") != expected_binary_sha256:
            failures.append("backend binary SHA256 is not pinned")
    expected_checkpoint = (
        None
        if expected_checkpoint_identity is None
        else _canonical_json(expected_checkpoint_identity)
    )
    if not isinstance(instance, Mapping):
        failures.append("instance binding is missing")
    else:
        instance_unsigned = dict(instance)
        binding_sha256 = instance_unsigned.pop("binding_sha256", None)
        if binding_sha256 != _canonical_sha256(instance_unsigned):
            failures.append("instance binding hash is invalid")
        if instance.get("formulation") != DISTQLDPC_FORMULATION:
            failures.append("instance formulation is wrong")
        if instance.get("n") != int(matrices["Hx"].shape[1]):
            failures.append("instance n does not replay")
        if instance.get("k") != int(matrices["Gx"].shape[0]):
            failures.append("instance k does not replay")
        if instance.get("max_weight") != int(max_weight):
            failures.append("instance threshold does not replay")
        if instance.get("matrix_files") != _matrix_records(matrices):
            failures.append("matrix file bindings do not replay")
        if instance.get("logical_detector") != _logical_detector_report(matrices):
            failures.append("logical detector completeness does not replay")
        if instance.get("backend") != backend:
            failures.append("instance/backend identities disagree")
        if instance.get("solver_execution") != {
            "policy": DISTQLDPC_EXECUTION_POLICY,
            "runtime_source": expected_runtime_source,
            "supervisor_python_argv": list(
                DISTQLDPC_SUPERVISOR_PYTHON_FLAGS
            ),
            "cardinality_mode": expected_cardinality_mode,
            "cardinality_argv": expected_cardinality_argv,
        }:
            failures.append("solver execution mode does not replay")
        if (
            expected_checkpoint_identity is not None
            and instance.get("checkpoint_identity") != expected_checkpoint
        ):
            failures.append("checkpoint identity does not replay")
    if evidence.get("schema_version") != DISTQLDPC_EVIDENCE_SCHEMA_VERSION:
        failures.append("evidence schema is wrong")
    if evidence.get("evidence_kind") != DISTQLDPC_EVIDENCE_KIND:
        failures.append("evidence kind is wrong")
    if evidence.get("formulation") != DISTQLDPC_FORMULATION:
        failures.append("evidence formulation is wrong")
    if evidence.get("max_weight") != int(max_weight):
        failures.append("evidence threshold is wrong")
    command_flags = evidence.get("command_flags")
    if not (
        isinstance(command_flags, list)
        and len(command_flags) == 1 + len(expected_cardinality_argv)
        and isinstance(command_flags[0], str)
        and re.fullmatch(r"-cpu-lim=[1-9]\d*", command_flags[0]) is not None
        and command_flags[1:] == expected_cardinality_argv
    ):
        failures.append("solver command flags do not replay")
    if evidence.get("outcome") != "exact":
        failures.append("evidence is not a terminal exact decision")
    if evidence.get("decision_complete") is not True:
        failures.append("exact decision is not marked complete")
    if evidence.get("retryable") is not False:
        failures.append("exact decision is incorrectly retryable")
    if evidence.get("timed_out") is not False:
        failures.append("timed-out evidence cannot be terminal")
    if evidence.get("returncode") != 0:
        failures.append("terminal evidence has a non-zero return code")
    if evidence.get("operator") is not None or evidence.get("objective") is not None:
        failures.append("DistQLDPC lower evidence must not claim a witness")
    stdout = evidence.get("stdout")
    stderr = evidence.get("stderr")
    if not isinstance(stdout, str) or not isinstance(stderr, str):
        failures.append("captured solver output is missing")
    else:
        if evidence.get("stdout_sha256") != hashlib.sha256(stdout.encode()).hexdigest():
            failures.append("stdout hash is invalid")
        if evidence.get("stderr_sha256") != hashlib.sha256(stderr.encode()).hexdigest():
            failures.append("stderr hash is invalid")
        parsed = parse_distqldpc_output(stdout)
        parse_failure = _exact_output_failure(
            parsed,
            returncode=int(evidence.get("returncode", -1)),
            n=int(matrices["Hx"].shape[1]),
        )
        if parse_failure is not None:
            failures.append(parse_failure)
        distance = parsed.get("d")
        if evidence.get("parsed_output") != parsed:
            failures.append("stored DistQLDPC parse does not replay")
        if evidence.get("exact_distance") != distance:
            failures.append("stored exact distance does not replay")
        if evidence.get("lower_bound") != distance or evidence.get("upper_bound") != distance:
            failures.append("stored exact bounds do not replay")
        if isinstance(distance, int) and not isinstance(distance, bool):
            expected_infeasible = distance > int(max_weight)
            if evidence.get("threshold_infeasible") is not expected_infeasible:
                failures.append("threshold-infeasible flag does not match exact distance")
    cleanup = evidence.get("cleanup")
    if isinstance(cleanup, Mapping) and cleanup.get("group_survived") is True:
        failures.append("solver process group survived cleanup")
    try:
        unsigned = dict(evidence)
        evidence_sha256 = unsigned.pop("evidence_sha256", None)
        if evidence_sha256 != _canonical_sha256(unsigned):
            failures.append("evidence hash is invalid")
    except (TypeError, ValueError):
        failures.append("evidence is not strict JSON")
    return failures


def verify_distqldpc_exact_evidence(
    evidence: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    max_weight: int,
    cardinality_mode: str = "default",
    expected_checkpoint_identity: Mapping[str, Any] | str | None = None,
    expected_binary_sha256: str = DISTQLDPC_PINNED_BINARY_SHA256,
    expected_source_commit: str = DISTQLDPC_PINNED_COMMIT,
) -> list[str]:
    """Replay a complete exact result without inferring a witness."""

    failures = _verify_exact_evidence(
        evidence,
        hx,
        hz,
        lx,
        lz,
        max_weight=max_weight,
        expected_cardinality_mode=cardinality_mode,
        expected_checkpoint_identity=expected_checkpoint_identity,
        expected_binary_sha256=expected_binary_sha256,
        expected_source_commit=expected_source_commit,
    )
    return failures


def verify_distqldpc_lower_evidence(
    evidence: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    max_weight: int,
    cardinality_mode: str = "default",
    expected_checkpoint_identity: Mapping[str, Any] | str | None = None,
    expected_binary_sha256: str = DISTQLDPC_PINNED_BINARY_SHA256,
    expected_source_commit: str = DISTQLDPC_PINNED_COMMIT,
) -> list[str]:
    """Replay an exact DistQLDPC result as the lower statement ``d>T``."""

    failures = verify_distqldpc_exact_evidence(
        evidence,
        hx,
        hz,
        lx,
        lz,
        max_weight=max_weight,
        cardinality_mode=cardinality_mode,
        expected_checkpoint_identity=expected_checkpoint_identity,
        expected_binary_sha256=expected_binary_sha256,
        expected_source_commit=expected_source_commit,
    )
    distance = evidence.get("exact_distance")
    if (
        isinstance(distance, bool)
        or not isinstance(distance, int)
        or distance <= int(max_weight)
        or evidence.get("threshold_infeasible") is not True
    ):
        failures.append("exact result does not prove the requested lower threshold")
    return failures


def _load_checkpoint(
    path: Path,
    *,
    binding: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    max_weight: int,
    cardinality_mode: str,
    expected_binary_sha256: str,
    expected_source_commit: str,
) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, UnicodeError, json.JSONDecodeError):
        return None
    if not isinstance(value, Mapping) or value.get("instance") != binding:
        return None
    if verify_distqldpc_lower_evidence(
        value,
        hx,
        hz,
        lx,
        lz,
        max_weight=max_weight,
        cardinality_mode=cardinality_mode,
        expected_binary_sha256=expected_binary_sha256,
        expected_source_commit=expected_source_commit,
    ):
        return None
    resumed = dict(value)
    resumed["resumed"] = True
    return _seal(resumed)


def solve_css_distance_distqldpc_lower(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    max_weight: int,
    timeout: float,
    binary: Path | str = DEFAULT_DISTQLDPC_EXE,
    cardinality_mode: str = "default",
    checkpoint_path: Path | str | None = None,
    progress_path: Path | str | None = None,
    checkpoint_identity: Mapping[str, Any] | str | None = None,
    resume: bool = True,
    cancel_event: Any | None = None,
    termination_grace_s: float = 2.0,
    expected_binary_sha256: str = DISTQLDPC_PINNED_BINARY_SHA256,
    expected_source_commit: str = DISTQLDPC_PINNED_COMMIT,
) -> dict[str, Any]:
    """Run one pinned DistQLDPC exact decision and expose only sound lower proof."""

    started = time.monotonic()
    hard_timeout = float(timeout)
    grace = float(termination_grace_s)
    cardinality_flags = distqldpc_cardinality_flags(cardinality_mode)
    if not math.isfinite(hard_timeout) or hard_timeout <= 0:
        raise ValueError("DistQLDPC timeout must be positive and finite")
    if not math.isfinite(grace) or grace < 0:
        raise ValueError("DistQLDPC termination grace must be finite and nonnegative")
    solver_deadline = started + hard_timeout
    cleanup_deadline = solver_deadline + grace
    if isinstance(max_weight, bool) or not isinstance(max_weight, int):
        raise ValueError("DistQLDPC max_weight must be an integer")
    matrices = distqldpc_matrix_bundle(hx, hz, lx, lz)
    n = int(matrices["Hx"].shape[1])
    if not 0 <= max_weight < n:
        raise ValueError("DistQLDPC max_weight must lie in [0,n)")
    try:
        backend = inspect_distqldpc_binary(
            binary,
            expected_binary_sha256=expected_binary_sha256,
            source_commit=expected_source_commit,
        )
    except DistQLDPCBackendUnavailable as exc:
        result = _base_result(
            binding=None,
            backend=None,
            max_weight=max_weight,
            hard_timeout_s=hard_timeout,
        )
        result.update({
            "outcome": "backend_unavailable",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "timed_out": False,
            "message": str(exc),
            "requested_binary": str(Path(binary).expanduser().absolute()),
            "elapsed_s": time.monotonic() - started,
        })
        return _seal(result)
    binding = _instance_binding(
        matrices,
        max_weight=max_weight,
        backend=backend,
        cardinality_mode=cardinality_mode,
        checkpoint_identity=checkpoint_identity,
    )
    checkpoint = Path(checkpoint_path) if checkpoint_path is not None else None
    progress = Path(progress_path) if progress_path is not None else None
    if checkpoint is not None and resume:
        reused = _load_checkpoint(
            checkpoint,
            binding=binding,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
            max_weight=max_weight,
            cardinality_mode=cardinality_mode,
            expected_binary_sha256=expected_binary_sha256,
            expected_source_commit=expected_source_commit,
        )
        if reused is not None:
            return reused

    base = _base_result(
        binding=binding,
        backend=backend,
        max_weight=max_weight,
        hard_timeout_s=hard_timeout,
    )
    process: subprocess.Popen[bytes] | None = None
    stdout = b""
    stderr = b""
    cleanup: dict[str, Any] | None = None
    termination: str | None = None
    if cancel_event is not None and cancel_event.is_set():
        result = dict(base)
        result.update({
            "outcome": "cancelled",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "timed_out": False,
            "message": "DistQLDPC was cancelled before launch",
            "elapsed_s": time.monotonic() - started,
        })
        return _seal(result)
    with tempfile.TemporaryDirectory(prefix="qcode-distqldpc-") as temporary:
        temporary_path = Path(temporary)
        prefix = temporary_path / "instance"
        for name, matrix in matrices.items():
            path = temporary_path / f"instance_{name}.txt"
            with path.open("wb") as stream:
                stream.write(_matrix_text(matrix))
                stream.flush()
                os.fsync(stream.fileno())
        # Leave a small interval for DistQLDPC's own fork/pipe parent to reap its
        # solver child before this adapter's authoritative outer hard wall.
        internal_limit = max(1, int(math.floor(max(1.0, hard_timeout - 2.0))))
        flags = [f"-cpu-lim={internal_limit}", *cardinality_flags]
        solver_command = [backend["resolved_path"], *flags, str(prefix)]
        supervisor_path = _DISTQLDPC_SUPERVISOR_PATH.resolve(strict=True)
        command = [
            str(Path(sys.executable).resolve(strict=True)),
            *DISTQLDPC_SUPERVISOR_PYTHON_FLAGS,
            str(supervisor_path),
            "--expected-parent-pid",
            str(os.getpid()),
            "--termination-grace-s",
            repr(grace),
            "--absolute-cleanup-deadline",
            repr(cleanup_deadline),
            "--",
            *solver_command,
        ]
        stdout_path = temporary_path / "stdout.txt"
        stderr_path = temporary_path / "stderr.txt"
        try:
            with stdout_path.open("wb") as stdout_stream, stderr_path.open(
                "wb",
            ) as stderr_stream:
                process = subprocess.Popen(
                    command,
                    stdin=subprocess.DEVNULL,
                    stdout=stdout_stream,
                    stderr=stderr_stream,
                    start_new_session=True,
                )
                if os.getpgid(process.pid) != process.pid:
                    raise RuntimeError("DistQLDPC did not establish a private session")
                deadline = solver_deadline
                last_progress_key: (
                    tuple[int | None, int | None, int | None] | None
                ) = None
                last_progress_persisted_at = -math.inf
                while process.poll() is None:
                    if cancel_event is not None and cancel_event.is_set():
                        termination = "cancelled"
                        break
                    now = time.monotonic()
                    remaining = deadline - now
                    if remaining <= 0:
                        termination = "hard_timeout"
                        break
                    if progress is not None:
                        stdout_stream.flush()
                        size = stdout_path.stat().st_size
                        if size <= _MAX_CAPTURE_BYTES:
                            try:
                                partial_stdout = stdout_path.read_text(
                                    encoding="utf-8",
                                    errors="strict",
                                )
                            except (OSError, UnicodeError):
                                partial_stdout = ""
                            parsed_progress = parse_distqldpc_output(partial_stdout)
                            progress_key = (
                                parsed_progress["d_lb"],
                                parsed_progress["d_ub"],
                                parsed_progress["o"],
                            )
                            if (
                                progress_key != last_progress_key
                                or now - last_progress_persisted_at >= 5.0
                            ):
                                progress_record = {
                                    "schema_version": 1,
                                    "kind": "qcode-distqldpc-live-progress",
                                    "proof_evidence": False,
                                    "instance_binding_sha256": (
                                        binding["binding_sha256"]
                                    ),
                                    "pid": int(process.pid),
                                    "elapsed_s": now - started,
                                    "d_lb": parsed_progress["d_lb"],
                                    "d_ub": parsed_progress["d_ub"],
                                    "o": parsed_progress["o"],
                                    "decision_complete": False,
                                }
                                _atomic_write_json(progress, progress_record)
                                last_progress_key = progress_key
                                last_progress_persisted_at = now
                    time.sleep(min(0.1, remaining))
                # The outer monotonic wall and cancellation token remain
                # authoritative even if the child exits between poll cycles.
                if termination is None:
                    if cancel_event is not None and cancel_event.is_set():
                        termination = "cancelled"
                    elif time.monotonic() >= deadline:
                        termination = "hard_timeout"
                if termination is not None:
                    cleanup = _terminate_process_group(
                    process,
                    grace_s=grace,
                    absolute_deadline=cleanup_deadline,
                )
                else:
                    process.wait()
                stdout_stream.flush()
                stderr_stream.flush()
            stdout = stdout_path.read_bytes()
            stderr = stderr_path.read_bytes()
        except (OSError, RuntimeError) as exc:
            if process is not None and (
                process.poll() is None
                or _process_group_exists(process.pid)
            ):
                cleanup = _terminate_process_group(
                    process,
                    grace_s=grace,
                    absolute_deadline=cleanup_deadline,
                )
            try:
                stdout = stdout_path.read_bytes()
                stderr = stderr_path.read_bytes()
            except OSError:
                stdout = b""
                stderr = b""
            result = dict(base)
            result.update({
                "outcome": "solver_error",
                "decision_complete": False,
                "threshold_infeasible": False,
                "retryable": True,
                "timed_out": False,
                "message": f"DistQLDPC could not run safely: {exc}",
                "cleanup": cleanup,
                "elapsed_s": time.monotonic() - started,
            })
            return _seal(result)

    assert process is not None and process.returncode is not None
    # DistQLDPC normally reaps its own solver child before its leader exits.
    # Check the known private process group before *any* output/error return:
    # a dead leader can otherwise leave a descendant alive when capture or
    # decoding fails.  Remember that this happened so a seemingly exact result
    # is rejected even when the cleanup itself succeeds.
    group_survived = _process_group_exists(process.pid)
    if group_survived:
        cleanup = _terminate_process_group(
            process,
            grace_s=grace,
            absolute_deadline=cleanup_deadline,
        )
    if len(stdout) > _MAX_CAPTURE_BYTES or len(stderr) > _MAX_CAPTURE_BYTES:
        result = dict(base)
        result.update({
            "outcome": "solver_error",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "timed_out": termination == "hard_timeout",
            "message": "DistQLDPC output exceeded the capture limit",
            "returncode": int(process.returncode),
            "cleanup": cleanup,
            "elapsed_s": time.monotonic() - started,
        })
        return _seal(result)
    try:
        stdout_text = stdout.decode("utf-8", errors="strict")
        stderr_text = stderr.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        result = dict(base)
        result.update({
            "outcome": "solver_error",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "timed_out": termination == "hard_timeout",
            "message": f"DistQLDPC output is not UTF-8: {exc}",
            "returncode": int(process.returncode),
            "cleanup": cleanup,
            "elapsed_s": time.monotonic() - started,
        })
        return _seal(result)
    parsed = parse_distqldpc_output(stdout_text)
    result = dict(base)
    result.update({
        "stdout": stdout_text,
        "stderr": stderr_text,
        "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
        "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
        "parsed_output": parsed,
        "returncode": int(process.returncode),
        "cleanup": cleanup,
        "command_flags": flags,
        "timed_out": termination == "hard_timeout",
        "elapsed_s": time.monotonic() - started,
    })
    if termination is not None:
        cleanup_failed = bool(
            isinstance(cleanup, Mapping)
            and cleanup.get("group_survived") is True
        )
        result.update({
            "outcome": "solver_error" if cleanup_failed else termination,
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "message": (
                "DistQLDPC process group survived mandatory cleanup"
                if cleanup_failed
                else (
                    "DistQLDPC was cancelled"
                    if termination == "cancelled"
                    else "DistQLDPC exceeded its authoritative outer hard wall"
                )
            ),
        })
        return _seal(result)
    result["cleanup"] = cleanup
    try:
        post_backend = inspect_distqldpc_binary(
            binary,
            expected_binary_sha256=expected_binary_sha256,
            source_commit=expected_source_commit,
        )
    except DistQLDPCBackendUnavailable as exc:
        post_backend = None
        identity_error = str(exc)
    else:
        identity_error = None
    try:
        post_runtime_source = _runtime_source_identity()
    except OSError as exc:
        post_runtime_source = None
        runtime_identity_error = str(exc)
    else:
        runtime_identity_error = None
    parse_failure = _exact_output_failure(
        parsed,
        returncode=int(process.returncode),
        n=n,
    )
    if parsed.get("reported_timeout") is True or parsed.get("unknown_final") is True:
        outcome = "hard_timeout"
        message = "DistQLDPC completed only an internal timeout/UNKNOWN result"
    elif post_backend != backend:
        outcome = "solver_error"
        message = identity_error or "DistQLDPC binary identity changed during the run"
    elif post_runtime_source != binding["solver_execution"]["runtime_source"]:
        outcome = "solver_error"
        message = (
            runtime_identity_error
            or "DistQLDPC adapter/supervisor source changed during the run"
        )
    elif group_survived:
        outcome = "solver_error"
        message = "DistQLDPC process group survived normal solver exit"
    elif parse_failure is not None:
        outcome = "solver_error"
        message = parse_failure
    else:
        outcome = "exact"
        message = None
    if outcome != "exact":
        result.update({
            "outcome": outcome,
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "timed_out": outcome == "hard_timeout",
            "message": message,
        })
        return _seal(result)
    distance = int(parsed["d"])
    result.update({
        "outcome": "exact",
        "decision_complete": True,
        "threshold_infeasible": distance > max_weight,
        "retryable": False,
        "timed_out": False,
        "message": None,
        "exact_distance": distance,
        "lower_bound": distance,
        "upper_bound": distance,
    })
    _seal(result)
    if _verify_exact_evidence(
        result,
        hx,
        hz,
        lx,
        lz,
        max_weight=max_weight,
        expected_cardinality_mode=cardinality_mode,
        expected_checkpoint_identity=checkpoint_identity,
        expected_binary_sha256=expected_binary_sha256,
        expected_source_commit=expected_source_commit,
    ):
        invalid = dict(result)
        invalid.update({
            "outcome": "solver_error",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "message": "DistQLDPC terminal evidence failed local replay",
        })
        return _seal(invalid)
    if (
        checkpoint is not None
        and result.get("threshold_infeasible") is True
    ):
        _atomic_write_json(checkpoint, result)
    return result


__all__ = [
    "DEFAULT_DISTQLDPC_EXE",
    "DISTQLDPC_CARDINALITY_MODES",
    "DISTQLDPC_EVIDENCE_KIND",
    "DISTQLDPC_EVIDENCE_SCHEMA_VERSION",
    "DISTQLDPC_FORMULATION",
    "DISTQLDPC_PINNED_BINARY_SHA256",
    "DISTQLDPC_PINNED_COMMIT",
    "DISTQLDPC_RETRYABLE_OUTCOMES",
    "DISTQLDPC_TERMINAL_OUTCOMES",
    "DistQLDPCBackendUnavailable",
    "distqldpc_cardinality_flags",
    "distqldpc_matrix_bundle",
    "inspect_distqldpc_binary",
    "parse_distqldpc_output",
    "solve_css_distance_distqldpc_lower",
    "verify_distqldpc_exact_evidence",
    "verify_distqldpc_lower_evidence",
]
