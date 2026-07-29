"""MILP-based exact distance computation for quantum codes.

Uses the integer-programming formulation introduced by Landahl, Anderson, and
Rice (arXiv:1108.5738, 2011) and reused by Bravyi et al. (arXiv:2308.07915,
which cites Landahl-Anderson-Rice as the source of the method) with
optimizations for use during evolutionary search:

  - Early exit when d drops to ``early_stop`` threshold
  - Cross-type early exit: skip d_X if d_Z already ≤ early_stop
  - Per-code total timeout (not just per-logical)
  - d_Z computed before d_X (cheaper to determine d is low)

Supports both CSS codes (``ilp_min_weight``, ``compute_distance_milp``)
and non-CSS codes (``ilp_min_weight_symplectic``,
``compute_distance_milp_symplectic``).

Core solver: HiGHS via ``scipy.optimize.milp``.  Thread-safe (no SIGALRM).
"""

from __future__ import annotations

import hashlib
import importlib.metadata
import json
import logging
import math
import multiprocessing
import os
import signal
import stat
import sys
import threading
import time
import traceback
from contextlib import contextmanager
from ctypes import CDLL, c_int, c_ulong, get_errno
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Literal, Mapping

import fcntl
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix, eye, hstack, vstack

from qldpc.objects import Pauli

logger = logging.getLogger(__name__)

_CSS_CHECKPOINT_KIND = "qcode-css-distance-milp-checkpoint"
_CSS_CHECKPOINT_SCHEMA_VERSION = 2
_SYMPLECTIC_CHECKPOINT_KIND = "qcode-symplectic-weight-checkpoint"
_SYMPLECTIC_CHECKPOINT_SCHEMA_VERSION = 1
_CSS_FORMULATION_REVISION = "css-logical-parity-binary-witness-v2"
try:
    _DISTANCE_MILP_SOURCE_SHA256 = hashlib.sha256(
        Path(__file__).read_bytes()
    ).hexdigest()
except OSError:
    _DISTANCE_MILP_SOURCE_SHA256 = None

_DIRECTION_STATUSES = {
    "optimal",
    "incumbent",
    "no_incumbent",
    "hard_timeout",
}


class CssCheckpointIncompatibleError(ValueError):
    """A regular checkpoint belongs to a different proof implementation."""


class CssCheckpointCorruptionError(ValueError):
    """A bound CSS checkpoint is malformed or internally inconsistent."""


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _canonical_json(value: Any) -> Any:
    """Return a strict JSON copy suitable for durable identity binding."""
    try:
        encoded = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise ValueError("checkpoint_identity must be strict JSON data") from exc
    return json.loads(encoded)


def _canonical_sha256(value: Any) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def _dependency_version(distribution: str) -> str:
    """Return a stable explicit version string for proof-environment binding."""
    try:
        return importlib.metadata.version(distribution)
    except Exception:
        return "unavailable"


def _implementation_fingerprint() -> dict[str, Any]:
    """Bind durable proofs to the exact implementation and solver stack."""
    if _DISTANCE_MILP_SOURCE_SHA256 is None:
        raise RuntimeError("cannot fingerprint distance_milp.py for checkpoint")
    fingerprint = {
        "distance_milp_py_sha256": _DISTANCE_MILP_SOURCE_SHA256,
        "formulation_revision": _CSS_FORMULATION_REVISION,
        "versions": {
            "numpy": _dependency_version("numpy"),
            "scipy": _dependency_version("scipy"),
            "qldpc": _dependency_version("qldpc"),
        },
    }
    fingerprint["fingerprint_sha256"] = _canonical_sha256(fingerprint)
    return fingerprint


def _binary_array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) % 2)
    digest = hashlib.sha256()
    digest.update(name.encode())
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _matrix_bundle_sha256(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> str:
    return _canonical_sha256({
        "hx": _binary_array_sha256("hx", hx),
        "hz": _binary_array_sha256("hz", hz),
        "lx": _binary_array_sha256("lx", lx),
        "lz": _binary_array_sha256("lz", lz),
    })


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    """Atomically replace one checkpoint and fsync both data and directory."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.tmp-{os.getpid()}-{threading.get_ident()}"
    )
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(
                value,
                stream,
                sort_keys=True,
                ensure_ascii=False,
                indent=2,
                allow_nan=False,
            )
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
        finally:
            os.close(directory_fd)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


@contextmanager
def _checkpoint_flock(path: Path | None):
    """Serialize the complete read/solve/write transaction for one candidate."""
    if path is None:
        yield
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = path.with_name(f".{path.name}.lock")
    flags = (
        os.O_RDWR
        | os.O_CREAT
        | os.O_CLOEXEC
        | os.O_NOFOLLOW
        | os.O_NONBLOCK
    )
    try:
        lock_fd = os.open(lock_path, flags, 0o600)
    except OSError as exc:
        raise ValueError(
            "CSS MILP checkpoint lock must be a non-symlink regular file"
        ) from exc
    locked = False
    try:
        if not stat.S_ISREG(os.fstat(lock_fd).st_mode):
            raise ValueError(
                "CSS MILP checkpoint lock must be a non-symlink regular file"
            )
        fcntl.flock(lock_fd, fcntl.LOCK_EX)
        locked = True
        yield
    finally:
        if locked:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
        os.close(lock_fd)


def _checkpoint_regular_file_exists(path: Path | None) -> bool:
    if path is None:
        return False
    try:
        file_status = os.lstat(path)
    except FileNotFoundError:
        return False
    except OSError as exc:
        raise ValueError(f"invalid CSS MILP checkpoint path: {path}") from exc
    if stat.S_ISLNK(file_status.st_mode) or not stat.S_ISREG(file_status.st_mode):
        raise ValueError(
            "CSS MILP checkpoint must be a non-symlink regular file"
        )
    return True


def _read_checkpoint_json(path: Path) -> Any:
    def reject_duplicate_keys(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate checkpoint key: {key!r}")
            value[key] = item
        return value

    def reject_non_finite(value):
        raise ValueError(f"non-finite checkpoint number: {value}")

    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        checkpoint_fd = os.open(path, flags)
    except OSError as exc:
        raise ValueError(f"invalid CSS MILP checkpoint: {path}") from exc
    try:
        if not stat.S_ISREG(os.fstat(checkpoint_fd).st_mode):
            raise ValueError(
                "CSS MILP checkpoint must be a non-symlink regular file"
            )
        with os.fdopen(checkpoint_fd, "r", encoding="utf-8") as stream:
            checkpoint_fd = -1
            try:
                return json.load(
                    stream,
                    object_pairs_hook=reject_duplicate_keys,
                    parse_constant=reject_non_finite,
                )
            except (UnicodeError, ValueError) as exc:
                raise CssCheckpointCorruptionError(
                    f"invalid CSS MILP checkpoint JSON: {path}"
                ) from exc
    finally:
        if checkpoint_fd >= 0:
            os.close(checkpoint_fd)


def _read_checkpoint_bytes(path: Path) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
    descriptor = os.open(path, flags)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ValueError(
                "CSS MILP checkpoint must be a non-symlink regular file"
            )
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _archive_incompatible_checkpoint(path: Path) -> Path:
    """Hard-link incompatible evidence aside before removing its working name."""

    payload = _read_checkpoint_bytes(path)
    digest = hashlib.sha256(payload).hexdigest()
    archive = path.with_name(
        f"{path.name}.incompatible-{digest}.json"
    )
    try:
        os.link(path, archive, follow_symlinks=False)
    except FileExistsError:
        pass
    if _read_checkpoint_bytes(archive) != payload:
        raise ValueError(
            "CSS MILP incompatible checkpoint archive collision"
        )
    os.unlink(path)
    directory_fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)
    return archive


def get_code_matrices(code):
    """Extract check matrices and logical operators from a qldpc BBCode.

    Returns (hx, hz, lx, lz) -- all binary numpy arrays.
    """
    hx = np.array(code.matrix_x, dtype=int) % 2
    hz = np.array(code.matrix_z, dtype=int) % 2
    lx = np.array(code.get_logical_ops(Pauli.X), dtype=int) % 2
    lz = np.array(code.get_logical_ops(Pauli.Z), dtype=int) % 2
    return hx, hz, lx, lz


def symplectic_weight_bound(code):
    """Upper bound on code distance from symplectic logical operator weights.

    Returns the minimum Hamming weight across all logical operators obtained
    via Gaussian elimination (the initial symplectic basis).  This is a valid
    upper bound on d because any logical operator witnesses d ≤ weight.

    Cost: milliseconds (no solver, just GF(2) linear algebra already done
    by qldpc internally).

    Returns:
        (d_upper, d_x_upper, d_z_upper) -- ints.
    """
    lx = np.array(code.get_logical_ops(Pauli.X), dtype=int) % 2
    lz = np.array(code.get_logical_ops(Pauli.Z), dtype=int) % 2

    d_x_upper = int(np.min(np.sum(lx, axis=1))) if lx.size > 0 else code.num_qudits
    d_z_upper = int(np.min(np.sum(lz, axis=1))) if lz.size > 0 else code.num_qudits
    d_upper = min(d_x_upper, d_z_upper)

    return d_upper, d_x_upper, d_z_upper


def symplectic_weight_witness(
    code,
    distance: int | None = None,
) -> dict[str, Any] | None:
    """Return a replayable minimum-basis logical witness.

    A raw row weight is not sufficient durable evidence: the selected row must
    commute with the applicable stabilizers and anticommute with an *actual*
    opposite-type logical row.  This helper deliberately returns ``None`` if
    the logical basis cannot supply that complete witness, so callers can fall
    back to MILP instead of treating an unbound number as a proof.
    """
    try:
        hx, hz, lx, lz = get_code_matrices(code)
        n = int(code.num_qudits)
    except Exception:
        return None
    if n <= 0:
        return None
    matrices = (hx, hz, lx, lz)
    if any(
        not isinstance(matrix, np.ndarray)
        or matrix.ndim != 2
        or matrix.shape[1] != n
        for matrix in matrices
    ):
        return None
    if distance is not None and (
        isinstance(distance, bool)
        or not isinstance(distance, (int, np.integer))
        or int(distance) < 1
    ):
        return None

    candidates: list[tuple[int, int, int, int, dict[str, Any]]] = []
    # The row itself is an X/Z logical.  Its opposite-type stabilizer checks
    # enforce commutation, while an opposite logical row proves non-triviality.
    for side, logicals, duals, checks in (
        ("X", lx, lz, hz),
        ("Z", lz, lx, hx),
    ):
        side_order = 0 if side == "X" else 1
        for index, raw_vector in enumerate(logicals):
            vector = np.asarray(raw_vector, dtype=np.uint8).reshape(-1) % 2
            weight = int(np.sum(vector))
            if weight < 1:
                continue
            if np.any((np.asarray(checks, dtype=np.uint8) @ vector) % 2):
                continue
            dual_index = next(
                (
                    candidate
                    for candidate, raw_dual in enumerate(duals)
                    if int(
                        np.dot(
                            np.asarray(raw_dual, dtype=np.uint8).reshape(-1) % 2,
                            vector,
                        )
                        % 2
                    )
                    == 1
                ),
                None,
            )
            if dual_index is None:
                continue
            witness = {
                "side": side,
                "index": int(index),
                "dual_side": "Z" if side == "X" else "X",
                "dual_index": int(dual_index),
                "weight": weight,
                "bits": [int(value) for value in vector],
            }
            candidates.append(
                (weight, side_order, int(index), int(dual_index), witness)
            )
    if not candidates:
        return None
    minimum = min(candidates, key=lambda item: item[:4])[-1]
    if distance is not None and minimum["weight"] != int(distance):
        return None
    return minimum


def _valid_symplectic_run_parameters(value: Any) -> bool:
    if not isinstance(value, dict) or set(value) != {
        "timeout_per_logical_s",
        "total_timeout_s",
        "hard_timeout_per_logical_s",
        "early_stop",
    }:
        return False
    for field in (
        "timeout_per_logical_s",
        "total_timeout_s",
        "hard_timeout_per_logical_s",
    ):
        budget = value[field]
        if budget is None:
            continue
        if (
            isinstance(budget, bool)
            or not isinstance(budget, (int, float))
            or not math.isfinite(budget)
            or budget <= 0
        ):
            return False
    early_stop = value["early_stop"]
    return early_stop is None or (
        not isinstance(early_stop, bool)
        and isinstance(early_stop, int)
        and early_stop >= 0
    )


def write_symplectic_weight_checkpoint(
    code,
    *,
    checkpoint_path: str | Path,
    checkpoint_identity: Mapping[str, Any] | str,
    witness: Mapping[str, Any],
    timeout_per_logical: int | float,
    total_timeout: int | float,
    hard_timeout_per_logical: int | float | None,
    early_stop: int | None,
    reset_incompatible_checkpoint: bool = False,
) -> dict[str, Any]:
    """Persist a formal checkpoint for a solver-free symplectic rejection."""
    canonical_witness = symplectic_weight_witness(code, witness.get("weight"))
    if canonical_witness is None or canonical_witness != dict(witness):
        raise ValueError("symplectic witness is not replayable from the code")
    hx, hz, lx, lz = get_code_matrices(code)
    n = int(code.num_qudits)
    k = int(code.dimension)
    proof_binding = {
        "candidate_identity": _canonical_json(checkpoint_identity),
        "n": n,
        "k": k,
        "matrix_bundle_sha256": _matrix_bundle_sha256(hx, hz, lx, lz),
        "implementation": _implementation_fingerprint(),
        "method": "logical-basis-symplectic-upper-bound",
        "witness_sha256": _canonical_sha256(canonical_witness),
    }
    proof_binding["binding_sha256"] = _canonical_sha256(proof_binding)
    run_parameters = {
        "timeout_per_logical_s": _checkpoint_budget(
            float(timeout_per_logical)
            if float(timeout_per_logical) > 0
            else float("inf")
        ),
        "total_timeout_s": _checkpoint_budget(
            float(total_timeout)
            if float(total_timeout) > 0
            else float("inf")
        ),
        "hard_timeout_per_logical_s": (
            float(hard_timeout_per_logical)
            if hard_timeout_per_logical is not None
            else None
        ),
        "early_stop": early_stop,
    }
    payload = {
        "kind": _SYMPLECTIC_CHECKPOINT_KIND,
        "schema_version": _SYMPLECTIC_CHECKPOINT_SCHEMA_VERSION,
        "created_at": _utc_now(),
        "updated_at": _utc_now(),
        "status": (
            "exact"
            if int(canonical_witness["weight"]) <= 2
            else "threshold_rejected"
        ),
        "proof_binding": proof_binding,
        "run_parameters": run_parameters,
        "symplectic_witness": canonical_witness,
    }
    path = Path(os.path.abspath(os.fspath(checkpoint_path)))
    with _checkpoint_flock(path):
        checkpoint_exists = _checkpoint_regular_file_exists(path)
        if checkpoint_exists:
            try:
                previous = _read_checkpoint_json(path)
            except CssCheckpointCorruptionError:
                if not reset_incompatible_checkpoint:
                    raise
                _archive_incompatible_checkpoint(path)
            else:
                expected_fields = set(payload)
                expected_parameter_fields = set(run_parameters)
                previous_parameters = (
                    previous.get("run_parameters")
                    if isinstance(previous, dict)
                    else None
                )
                compatible = (
                    isinstance(previous, dict)
                    and set(previous) == expected_fields
                    and previous.get("kind") == _SYMPLECTIC_CHECKPOINT_KIND
                    and previous.get("schema_version")
                    == _SYMPLECTIC_CHECKPOINT_SCHEMA_VERSION
                    and isinstance(previous.get("created_at"), str)
                    and isinstance(previous.get("updated_at"), str)
                    and previous.get("status") == payload["status"]
                    and previous.get("proof_binding") == proof_binding
                    and _valid_symplectic_run_parameters(previous_parameters)
                    and set(previous_parameters) == expected_parameter_fields
                    and previous.get("symplectic_witness") == canonical_witness
                )
                if not compatible:
                    if not reset_incompatible_checkpoint:
                        raise CssCheckpointIncompatibleError(
                            "Stage 1 checkpoint is incompatible with the "
                            "symplectic proof"
                        )
                    _archive_incompatible_checkpoint(path)
        _atomic_write_json(path, payload)
    return payload


def ilp_min_weight(
    check_matrix,
    logical_op,
    timeout=30,
    *,
    return_witness: bool = False,
):
    """Find minimum-weight operator orthogonal to checks, anticommuting with logical_op.

    Formulation: binary variables x_j for each of n qubits, with mod-2
    constraints encoded as integer equalities using slack variables.

    Args:
        check_matrix: (m, n) binary matrix of stabilizer checks.
        logical_op: (n,) binary vector of a logical operator.
        timeout: solver time limit in seconds.

    Returns:
        By default, a backwards-compatible ``(weight, optimal)`` tuple.
        With ``return_witness=True``, returns
        ``(weight, optimal, binary_witness)``. ``weight`` and ``witness`` are
        both ``None`` when no feasible incumbent was found.
    """
    m, n = check_matrix.shape
    num_vars = n + m + 1  # [x_0..x_{n-1}, s_0..s_{m-1}, t]

    # Objective: minimize Hamming weight
    c = np.zeros(num_vars)
    c[:n] = 1.0

    # Sparse constraint matrix: [H, -2I, 0] plus the logical parity row.
    # Keeping this sparse materially lowers memory use when many independent
    # logical directions are solved in parallel.
    stabilizer_rows = hstack((
        csr_matrix(check_matrix, dtype=float),
        -2.0 * eye(m, format="csr"),
        csr_matrix((m, 1), dtype=float),
    ), format="csr")
    logical_row = hstack((
        csr_matrix(np.asarray(logical_op, dtype=float).reshape(1, n)),
        csr_matrix((1, m), dtype=float),
        csr_matrix([[-2.0]]),
    ), format="csr")
    constraint_matrix = vstack((stabilizer_rows, logical_row), format="csr")
    b_lb = np.zeros(m + 1)
    b_ub = np.zeros(m + 1)
    b_lb[m] = 1
    b_ub[m] = 1
    constraints = LinearConstraint(constraint_matrix, b_lb, b_ub)

    # Bounds
    lb = np.zeros(num_vars)
    ub = np.ones(num_vars)
    for r in range(m):
        ub[n + r] = np.ceil(np.sum(check_matrix[r]) / 2)
    ub[n + m] = np.ceil(np.sum(logical_op) / 2)

    bounds = Bounds(lb, ub)
    integrality = np.ones(num_vars)

    opts = {"presolve": True}
    if 0 < timeout < 1e9:
        opts["time_limit"] = timeout

    result = milp(
        c=c,
        constraints=constraints,
        integrality=integrality,
        bounds=bounds,
        options=opts,
    )

    if result.x is not None:
        w = int(round(result.fun))
        if return_witness:
            raw_witness = np.asarray(result.x[:n], dtype=float)
            rounded = np.rint(raw_witness)
            if (
                not np.all(np.isfinite(raw_witness))
                or not np.allclose(raw_witness, rounded, atol=1e-6, rtol=0)
                or not np.all((rounded == 0) | (rounded == 1))
            ):
                raise RuntimeError("CSS MILP returned a non-binary witness")
            return w, result.success, [int(value) for value in rounded]
        return w, result.success  # success=True means proven optimal
    if return_witness:
        return None, False, None
    return None, False


def _validate_css_direction_witness(
    check_matrix: np.ndarray,
    logical_op: np.ndarray,
    weight: int,
    witness: Any,
) -> list[int]:
    """Replay all CSS feasibility conditions and return canonical witness."""
    n = int(check_matrix.shape[1])
    if isinstance(weight, bool) or not isinstance(weight, (int, np.integer)):
        raise ValueError("CSS MILP feasible witness has invalid weight")
    weight = int(weight)
    if not 1 <= weight <= n:
        raise ValueError("CSS MILP feasible witness has invalid weight")
    if not isinstance(witness, (list, tuple, np.ndarray)) or len(witness) != n:
        raise ValueError("CSS MILP feasible witness has invalid shape")
    canonical: list[int] = []
    for value in witness:
        if (
            isinstance(value, (bool, np.bool_))
            or not isinstance(value, (int, np.integer))
            or int(value) not in (0, 1)
        ):
            raise ValueError("CSS MILP feasible witness is not binary")
        canonical.append(int(value))
    vector = np.asarray(canonical, dtype=np.uint8)
    if int(np.sum(vector)) != weight:
        raise ValueError("CSS MILP feasible witness weight mismatch")
    checks = np.asarray(check_matrix, dtype=np.uint8) % 2
    if np.any((checks @ vector) % 2):
        raise ValueError("CSS MILP feasible witness violates check parity")
    logical = np.asarray(logical_op, dtype=np.uint8).reshape(-1) % 2
    if logical.shape != (n,) or int(np.dot(logical, vector) % 2) != 1:
        raise ValueError("CSS MILP feasible witness violates logical parity")
    return canonical


def replay_css_direction_witness(
    check_matrix: np.ndarray,
    logical_op: np.ndarray,
    weight: int,
    witness: Any,
) -> list[int]:
    """Public verifier for a self-contained CSS direction witness."""
    return _validate_css_direction_witness(
        check_matrix, logical_op, weight, witness
    )


def _set_linux_parent_death_signal(expected_parent_pid: int) -> None:
    """SIGKILL this worker if its creating process dies, including arm race."""
    if not sys.platform.startswith("linux"):
        return
    libc = CDLL(None, use_errno=True)
    prctl = libc.prctl
    prctl.restype = c_int
    result = prctl(
        c_int(1),  # PR_SET_PDEATHSIG
        c_ulong(signal.SIGKILL),
        c_ulong(0),
        c_ulong(0),
        c_ulong(0),
    )
    if result != 0:
        error_number = get_errno()
        raise OSError(error_number, os.strerror(error_number))
    # The parent can die between clone() and prctl(). In that race the kernel
    # cannot deliver the newly armed signal, so fail closed after checking PPID.
    if os.getppid() != expected_parent_pid:
        os.kill(os.getpid(), signal.SIGKILL)
        os._exit(128 + signal.SIGKILL)


def _css_direction_worker(
    connection,
    expected_parent_pid: int,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> None:
    """Serve CSS logical-direction solves inside a terminable child process."""
    _set_linux_parent_death_signal(expected_parent_pid)
    try:
        while True:
            message = connection.recv()
            if message is None:
                return
            task_id, side, index, timeout = message
            try:
                if side == "Z":
                    result = ilp_min_weight(
                        hx, lx[index], timeout=timeout, return_witness=True
                    )
                elif side == "X":
                    result = ilp_min_weight(
                        hz, lz[index], timeout=timeout, return_witness=True
                    )
                else:
                    raise ValueError(f"unknown CSS logical direction: {side!r}")
            except BaseException as exc:
                connection.send((
                    "error",
                    task_id,
                    type(exc).__name__,
                    str(exc),
                    traceback.format_exc(),
                ))
            else:
                connection.send(
                    ("result", task_id, result[0], result[1], result[2])
                )
    except (EOFError, BrokenPipeError, OSError):
        return
    finally:
        connection.close()


class _HardWallCssDirectionSolver:
    """Reuse one spawned worker while retaining a kill boundary per direction."""

    def __init__(
        self,
        hx: np.ndarray,
        hz: np.ndarray,
        lx: np.ndarray,
        lz: np.ndarray,
    ):
        self._arrays = (hx, hz, lx, lz)
        self._context = multiprocessing.get_context("spawn")
        self._connection = None
        self._process = None
        self._task_id = 0

    def _start(self) -> None:
        if self._process is not None and self._process.is_alive():
            return
        self._stop()
        parent, child = self._context.Pipe(duplex=True)
        process = self._context.Process(
            target=_css_direction_worker,
            args=(child, os.getpid(), *self._arrays),
            daemon=True,
            name="qcode-css-milp-direction",
        )
        process.start()
        child.close()
        self._connection = parent
        self._process = process

    def _stop(self) -> None:
        connection = self._connection
        process = self._process
        self._connection = None
        self._process = None
        if connection is not None:
            try:
                connection.close()
            except OSError:
                pass
        if process is None:
            return
        if process.is_alive():
            process.terminate()
            process.join(timeout=2)
        if process.is_alive():
            process.kill()
            process.join(timeout=2)
        else:
            process.join(timeout=0)
        process.close()

    def solve(
        self,
        side: str,
        index: int,
        *,
        soft_timeout: float,
        hard_timeout: float,
    ) -> tuple[int | None, bool, str, list[int] | None]:
        self._start()
        assert self._connection is not None
        self._task_id += 1
        task_id = self._task_id
        try:
            self._connection.send((task_id, side, index, soft_timeout))
        except (BrokenPipeError, EOFError, OSError) as exc:
            self._stop()
            raise RuntimeError("CSS MILP hard-wall worker exited before solve") from exc

        if not self._connection.poll(hard_timeout):
            self._stop()
            return None, False, "hard_timeout", None
        try:
            message = self._connection.recv()
        except (EOFError, OSError) as exc:
            self._stop()
            raise RuntimeError("CSS MILP hard-wall worker exited without result") from exc
        if not message or message[1] != task_id:
            self._stop()
            raise RuntimeError("CSS MILP hard-wall worker protocol mismatch")
        if message[0] == "error":
            _, _, error_type, error, worker_traceback = message
            raise RuntimeError(
                f"CSS MILP worker failed: {error_type}: {error}\n{worker_traceback}"
            )
        if message[0] != "result":
            self._stop()
            raise RuntimeError("CSS MILP hard-wall worker returned invalid message")
        _, _, weight, optimal, witness = message
        if weight is None:
            if witness is not None:
                self._stop()
                raise RuntimeError("CSS MILP worker returned witness without weight")
            return None, False, "no_incumbent", None
        return (
            int(weight),
            bool(optimal),
            "optimal" if optimal else "incumbent",
            witness,
        )

    def close(self) -> None:
        if self._connection is not None and self._process is not None:
            try:
                self._connection.send(None)
            except (BrokenPipeError, EOFError, OSError):
                pass
            self._process.join(timeout=2)
        self._stop()

    def __enter__(self) -> "_HardWallCssDirectionSolver":
        return self

    def __exit__(self, *_exc_info) -> None:
        self.close()


@dataclass(frozen=True)
class CssExactReplayResult:
    """Outcome of an independent replay of all CSS logical directions.

    ``unavailable`` means that the fresh solver could not complete within the
    supplied wall budgets (or was otherwise unavailable), so the stored claim
    must remain unresolved and may be retried.  ``mismatch`` means that the
    stored direction set is malformed or that a fresh proven optimum differs
    from the stored weight; callers should treat that evidence as corrupt.
    """

    status: Literal["exact", "unavailable", "mismatch"]
    reason: str
    checked_directions: int
    total_directions: int
    elapsed_s: float
    direction_id: str | None = None
    expected_weight: int | None = None
    observed_weight: int | None = None

    @property
    def exact(self) -> bool:
        return self.status == "exact"

    @property
    def unavailable(self) -> bool:
        return self.status == "unavailable"

    @property
    def mismatch(self) -> bool:
        return self.status == "mismatch"


def replay_css_exact_directions(
    code,
    direction_records: Mapping[str, Mapping[str, Any]],
    *,
    timeout_per_logical: int | float = 30,
    total_timeout: int | float = 120,
    hard_timeout_per_logical: int | float = 35,
) -> CssExactReplayResult:
    """Independently prove stored CSS direction weights are exact.

    This verifier deliberately ignores every stored solver status and never
    resumes a checkpoint.  It creates a new killable HiGHS worker and solves
    every canonical Z/X logical direction again.  Exactness is established
    only when every fresh solve reports ``optimal``, returns a replayable
    witness, and its optimum equals the corresponding stored weight.

    A solver timeout/failure returns ``status="unavailable"`` so callers can
    retry with a larger budget.  A malformed record set or a fresh optimum
    different from the stored value returns ``status="mismatch"``.
    """

    def positive_finite_budget(name: str, raw: int | float) -> float:
        if (
            isinstance(raw, bool)
            or not isinstance(raw, (int, float))
            or not math.isfinite(float(raw))
            or float(raw) <= 0
        ):
            raise ValueError(f"{name} must be a positive finite number")
        return float(raw)

    soft_budget = positive_finite_budget(
        "timeout_per_logical", timeout_per_logical
    )
    total_budget = positive_finite_budget("total_timeout", total_timeout)
    hard_budget = positive_finite_budget(
        "hard_timeout_per_logical", hard_timeout_per_logical
    )
    started = time.monotonic()

    def result(
        status: Literal["exact", "unavailable", "mismatch"],
        reason: str,
        checked: int,
        total: int,
        *,
        direction_id: str | None = None,
        expected_weight: int | None = None,
        observed_weight: int | None = None,
    ) -> CssExactReplayResult:
        return CssExactReplayResult(
            status=status,
            reason=reason,
            checked_directions=checked,
            total_directions=total,
            elapsed_s=max(0.0, time.monotonic() - started),
            direction_id=direction_id,
            expected_weight=expected_weight,
            observed_weight=observed_weight,
        )

    if not isinstance(direction_records, Mapping):
        return result(
            "mismatch",
            "direction_records_not_mapping",
            0,
            0,
        )

    try:
        n = int(code.num_qudits)
        k = int(code.dimension)
        hx, hz, lx, lz = get_code_matrices(code)
    except Exception:
        return result("unavailable", "code_matrices_unavailable", 0, 0)
    total_directions = 2 * k
    if n < 1 or k < 0:
        return result(
            "mismatch",
            "invalid_code_dimensions",
            0,
            total_directions,
        )
    matrices = (hx, hz, lx, lz)
    if any(
        not isinstance(matrix, np.ndarray)
        or matrix.ndim != 2
        or matrix.shape[1] != n
        for matrix in matrices
    ) or lx.shape[0] != k or lz.shape[0] != k:
        return result(
            "unavailable",
            "code_matrices_invalid",
            0,
            total_directions,
        )

    expected_ids = [
        f"{side}:{index}"
        for side in ("Z", "X")
        for index in range(k)
    ]
    try:
        record_ids = set(direction_records)
    except Exception:
        return result(
            "mismatch",
            "direction_record_ids_invalid",
            0,
            total_directions,
        )
    if record_ids != set(expected_ids):
        return result(
            "mismatch",
            "direction_record_set_mismatch",
            0,
            total_directions,
        )

    expected_weights: dict[str, int] = {}
    for direction_id in expected_ids:
        record = direction_records.get(direction_id)
        if not isinstance(record, Mapping):
            return result(
                "mismatch",
                "direction_record_not_mapping",
                0,
                total_directions,
                direction_id=direction_id,
            )
        side, raw_index = direction_id.split(":", 1)
        index = int(raw_index)
        record_index = record.get("index")
        weight = record.get("weight")
        if (
            record.get("side") != side
            or isinstance(record_index, bool)
            or not isinstance(record_index, (int, np.integer))
            or int(record_index) != index
            or isinstance(weight, bool)
            or not isinstance(weight, (int, np.integer))
            or not 1 <= int(weight) <= n
        ):
            return result(
                "mismatch",
                "direction_record_invalid",
                0,
                total_directions,
                direction_id=direction_id,
            )
        expected_weights[direction_id] = int(weight)

    checked = 0
    if total_directions == 0:
        return result("exact", "all_directions_replayed", 0, 0)

    try:
        with _HardWallCssDirectionSolver(hx, hz, lx, lz) as solver:
            for direction_id in expected_ids:
                elapsed = time.monotonic() - started
                remaining = total_budget - elapsed
                if remaining <= 0:
                    return result(
                        "unavailable",
                        "total_wall_timeout",
                        checked,
                        total_directions,
                        direction_id=direction_id,
                    )
                direction_hard_budget = min(hard_budget, remaining)
                direction_soft_budget = min(
                    soft_budget, direction_hard_budget
                )
                side, raw_index = direction_id.split(":", 1)
                index = int(raw_index)
                try:
                    weight, optimal, outcome, witness = solver.solve(
                        side,
                        index,
                        soft_timeout=direction_soft_budget,
                        hard_timeout=direction_hard_budget,
                    )
                except Exception:
                    return result(
                        "unavailable",
                        "solver_unavailable",
                        checked,
                        total_directions,
                        direction_id=direction_id,
                    )
                if time.monotonic() - started > total_budget:
                    return result(
                        "unavailable",
                        "total_wall_timeout",
                        checked,
                        total_directions,
                        direction_id=direction_id,
                    )
                if outcome != "optimal" or optimal is not True or weight is None:
                    reason = (
                        "direction_hard_timeout"
                        if outcome == "hard_timeout"
                        else "direction_optimum_unavailable"
                    )
                    return result(
                        "unavailable",
                        reason,
                        checked,
                        total_directions,
                        direction_id=direction_id,
                        observed_weight=(
                            int(weight) if weight is not None else None
                        ),
                    )
                checks = hx if side == "Z" else hz
                logical = lx[index] if side == "Z" else lz[index]
                try:
                    _validate_css_direction_witness(
                        checks, logical, int(weight), witness
                    )
                except (TypeError, ValueError):
                    return result(
                        "unavailable",
                        "solver_witness_invalid",
                        checked,
                        total_directions,
                        direction_id=direction_id,
                        observed_weight=int(weight),
                    )
                expected_weight = expected_weights[direction_id]
                if int(weight) != expected_weight:
                    return result(
                        "mismatch",
                        "optimal_weight_mismatch",
                        checked,
                        total_directions,
                        direction_id=direction_id,
                        expected_weight=expected_weight,
                        observed_weight=int(weight),
                    )
                checked += 1
    except Exception:
        return result(
            "unavailable",
            "solver_unavailable",
            checked,
            total_directions,
        )
    return result(
        "exact",
        "all_directions_replayed",
        checked,
        total_directions,
    )


def _legacy_direction_solve(
    checks: np.ndarray,
    logical: np.ndarray,
    *,
    timeout: float,
) -> tuple[int | None, bool, list[int] | None]:
    """Request a witness while tolerating old two-field test doubles."""
    raw = ilp_min_weight(
        checks,
        logical,
        timeout=timeout,
        return_witness=True,
    )
    if not isinstance(raw, tuple) or len(raw) not in {2, 3}:
        raise RuntimeError("CSS MILP direction solver returned invalid data")
    weight, optimal = raw[:2]
    witness = raw[2] if len(raw) == 3 else None
    if weight is None:
        if witness is not None:
            raise RuntimeError("CSS MILP returned witness without a weight")
        return None, False, None
    weight = int(weight)
    if witness is not None:
        witness = _validate_css_direction_witness(
            checks, logical, weight, witness
        )
    return weight, bool(optimal), witness


def _compute_distance_milp_legacy(
    code,
    *,
    timeout_per_logical: int = 30,
    total_timeout: int = 120,
    early_stop: int | None = 4,
    verbose: bool = False,
) -> tuple[int, dict]:
    """Compute exact code distance via MILP with early-exit optimizations.

    Optimizations over the basic ILP approach:
    1. Stops as soon as d drops to ``early_stop`` (most bad codes have d=2-4).
    2. Computes d_Z first; skips d_X if d_Z ≤ early_stop.
    3. Respects a total time budget across all logicals.
    4. Adapts per-logical timeout to ensure broad coverage: when k is large,
       uses shorter per-logical timeouts to check more logicals (coverage
       matters more than per-logical optimality for finding min-weight).

    Args:
        code: qldpc BBCode instance.
        timeout_per_logical: Max seconds per individual ILP solve.
        total_timeout: Max total seconds for the entire distance computation.
        early_stop: Stop immediately when d ≤ this value. Pass ``None`` to
            disable early stopping and iterate over every logical (required
            when the goal is to certify an exact distance).
        verbose: Log progress.

    Returns:
        (d, details) where d is the exact distance (or best upper bound on
        timeout) and details contains d_x, d_z, num_logicals_checked, time_s,
        and exact (bool indicating whether the result is provably exact).
    """
    # Convert 0 = unlimited to effectively infinite budget
    if timeout_per_logical <= 0:
        timeout_per_logical = float("inf")
    if total_timeout <= 0:
        total_timeout = float("inf")

    n = code.num_qudits
    k = code.dimension
    if k == 0:
        return n, {"d_x": n, "d_z": n, "k": 0, "exact": True,
                    "num_logicals_checked": 0, "total_logicals": 0,
                    "time_s": 0.0}

    hx, hz, lx, lz = get_code_matrices(code)
    t_start = time.monotonic()
    logicals_checked = 0
    logicals_optimal = 0   # Proven optimal by solver
    logicals_incumbent = 0  # Feasible solution found but not proven optimal
    all_solved = True  # Track whether all logicals were solved (no timeouts)
    feasible_witnesses: list[tuple[int, int, int, dict[str, Any]]] = []

    # Per-logical timeout is passed through unmodified.  The caller
    # (evaluator) sets the budget; total_timeout is enforced via the
    # _remaining() check before each logical.  This avoids the old
    # adaptive formula that starved per-logical time when k was large
    # (e.g. k=24 with total=300s → only 6s/logical, far too low).

    def _remaining():
        return max(0, total_timeout - (time.monotonic() - t_start))

    # --- Z-distance: min-weight Z-op commuting with X-checks ---
    d_z = n
    any_z_found = False  # Any feasible solution (optimal or incumbent)
    for i in range(k):
        remaining = _remaining()
        if remaining <= 0:
            all_solved = False
            break
        timeout = min(timeout_per_logical, remaining)
        w, optimal, witness = _legacy_direction_solve(
            hx, lx[i], timeout=timeout
        )
        logicals_checked += 1
        if w is not None:
            d_z = min(d_z, w)
            any_z_found = True
            if witness is not None:
                feasible_witnesses.append((
                    int(w),
                    0,
                    i,
                    {
                        "side": "Z",
                        "index": i,
                        "weight": int(w),
                        "bits": witness,
                    },
                ))
            if optimal:
                logicals_optimal += 1
            else:
                logicals_incumbent += 1
                all_solved = False
            if verbose:
                tag = "" if optimal else " (incumbent)"
                logger.info("Z[%d]: d=%d%s (%.1fs)", i, w, tag,
                            time.monotonic() - t_start)
        else:
            all_solved = False
            if verbose:
                logger.info("Z[%d]: no solution (%.1fs)", i,
                            time.monotonic() - t_start)
        if early_stop is not None and any_z_found and d_z <= early_stop:
            break

    # --- Cross-type early exit ---
    # d = min(d_X, d_Z). If d_Z is already very low, no point computing d_X.
    if early_stop is not None and any_z_found and d_z <= early_stop:
        d = d_z
        elapsed = time.monotonic() - t_start
        # d_z ≤ early_stop was found as a feasible solution (optimal or
        # incumbent). Either way, d ≤ d_z is a valid upper bound.
        # exact=False because d_x was not computed -- we cannot prove d_x >= d_z.
        return d, {
            "d_x": n,  # Not computed
            "d_z": d_z,
            "k": k,
            "exact": False,
            "d_x_computed": False,
            "num_logicals_checked": logicals_checked,
            "logicals_optimal": logicals_optimal,
            "logicals_incumbent": logicals_incumbent,
            "total_logicals": 2 * k,
            "time_s": elapsed,
            "timeout_per_logical": timeout_per_logical,
            "minimum_direction_witness": (
                min(feasible_witnesses, key=lambda item: item[:3])[-1]
                if feasible_witnesses
                else None
            ),
        }

    # --- X-distance: min-weight X-op commuting with Z-checks ---
    d_x = n
    any_x_found = False
    x_phase_started = False
    for i in range(k):
        remaining = _remaining()
        if remaining <= 0:
            all_solved = False
            break
        x_phase_started = True
        timeout = min(timeout_per_logical, remaining)
        w, optimal, witness = _legacy_direction_solve(
            hz, lz[i], timeout=timeout
        )
        logicals_checked += 1
        if w is not None:
            d_x = min(d_x, w)
            any_x_found = True
            if witness is not None:
                feasible_witnesses.append((
                    int(w),
                    1,
                    i,
                    {
                        "side": "X",
                        "index": i,
                        "weight": int(w),
                        "bits": witness,
                    },
                ))
            if optimal:
                logicals_optimal += 1
            else:
                logicals_incumbent += 1
                all_solved = False
            if verbose:
                tag = "" if optimal else " (incumbent)"
                logger.info("X[%d]: d=%d%s (%.1fs)", i, w, tag,
                            time.monotonic() - t_start)
        else:
            all_solved = False
            if verbose:
                logger.info("X[%d]: no solution (%.1fs)", i,
                            time.monotonic() - t_start)
        # Early exit: d_X already below d_Z, no need to check more
        if early_stop is not None and any_x_found and d_x <= early_stop:
            if i + 1 < k:
                all_solved = False
            break

    elapsed = time.monotonic() - t_start

    # A time limit with no incumbent proves no distance bound. ``early_stop``
    # only controls when a found solution ends the search; it does not constrain
    # the MILP to weights at or below that threshold.
    if not any_z_found and not any_x_found:
        return n, {
            "d_x": 0,
            "d_z": 0,
            "k": k,
            "exact": False,
            "d_x_computed": x_phase_started,
            "num_logicals_checked": logicals_checked,
            "logicals_optimal": logicals_optimal,
            "logicals_incumbent": logicals_incumbent,
            "total_logicals": 2 * k,
            "time_s": elapsed,
            "timeout_per_logical": timeout_per_logical,
            "all_timeout": True,
            "no_incumbent": True,
            "distance_status": "unknown",
            "d_is_lower_bound": False,
            "minimum_direction_witness": None,
        }

    # Use the best feasible values found. Unsolved sides stay at n
    # (trivially valid upper bound).
    d = min(d_x, d_z)

    return d, {
        "d_x": d_x if any_x_found else 0,
        "d_z": d_z if any_z_found else 0,
        "k": k,
        "exact": all_solved and logicals_checked == logicals_optimal == 2 * k,
        "d_x_computed": x_phase_started,
        "num_logicals_checked": logicals_checked,
        "logicals_optimal": logicals_optimal,
        "logicals_incumbent": logicals_incumbent,
        "total_logicals": 2 * k,
        "time_s": elapsed,
        "timeout_per_logical": timeout_per_logical,
        "minimum_direction_witness": (
            min(feasible_witnesses, key=lambda item: item[:3])[-1]
            if feasible_witnesses
            else None
        ),
    }


def _checkpoint_budget(value: float) -> float | None:
    return float(value) if math.isfinite(value) else None


def _validated_checkpoint_budget(field: str, value: Any) -> float | None:
    if value is None:
        return None
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(value)
        or value <= 0
    ):
        raise CssCheckpointCorruptionError(
            f"CSS MILP checkpoint has invalid bound budget {field}"
        )
    return float(value)


def _is_budget_upgrade(previous: float | None, current: float | None) -> bool:
    """Allow completed proofs to survive a monotonic timeout-budget increase."""
    if previous is None:
        return current is None
    return current is None or float(current) >= float(previous)


def _compute_distance_milp_durable(
    code,
    *,
    timeout_per_logical: int = 30,
    total_timeout: int = 120,
    early_stop: int | None = 4,
    verbose: bool = False,
    checkpoint_path: str | Path | None = None,
    resume: bool = True,
    hard_timeout_per_logical: float | None = None,
    checkpoint_identity: Mapping[str, Any] | str | None = None,
    reset_incompatible_checkpoint: bool = False,
) -> tuple[int, dict]:
    """Serialize each candidate's complete durable checkpoint transaction."""
    path = (
        Path(os.path.abspath(os.fspath(checkpoint_path)))
        if checkpoint_path is not None
        else None
    )
    with _checkpoint_flock(path):
        checkpoint_exists = _checkpoint_regular_file_exists(path)
        arguments = {
            "timeout_per_logical": timeout_per_logical,
            "total_timeout": total_timeout,
            "early_stop": early_stop,
            "verbose": verbose,
            "checkpoint_path": path,
            "hard_timeout_per_logical": hard_timeout_per_logical,
            "checkpoint_identity": checkpoint_identity,
        }
        try:
            return _compute_distance_milp_durable_locked(
                code,
                checkpoint_exists=checkpoint_exists,
                resume=resume,
                **arguments,
            )
        except (
            CssCheckpointCorruptionError,
            CssCheckpointIncompatibleError,
        ) as exc:
            if (
                not reset_incompatible_checkpoint
                or path is None
                or not checkpoint_exists
            ):
                raise
            archive = _archive_incompatible_checkpoint(path)
            distance, details = _compute_distance_milp_durable_locked(
                code,
                checkpoint_exists=False,
                resume=False,
                **arguments,
            )
            details["checkpoint_reset"] = True
            details["checkpoint_reset_reason"] = str(exc)
            details["checkpoint_incompatible_archive"] = str(archive)
            return distance, details


def _compute_distance_milp_durable_locked(
    code,
    *,
    timeout_per_logical: int = 30,
    total_timeout: int = 120,
    early_stop: int | None = 4,
    verbose: bool = False,
    checkpoint_path: str | Path | None = None,
    checkpoint_exists: bool = False,
    resume: bool = True,
    hard_timeout_per_logical: float | None = None,
    checkpoint_identity: Mapping[str, Any] | str | None = None,
) -> tuple[int, dict]:
    """Durable CSS MILP loop with direction checkpoints and killable solves."""
    timeout_per_logical = float(timeout_per_logical)
    total_timeout = float(total_timeout)
    if math.isnan(timeout_per_logical):
        raise ValueError("timeout_per_logical must not be NaN")
    if math.isnan(total_timeout):
        raise ValueError("total_timeout must not be NaN")
    if timeout_per_logical <= 0:
        timeout_per_logical = float("inf")
    if total_timeout <= 0:
        total_timeout = float("inf")
    if early_stop is not None:
        if isinstance(early_stop, bool):
            raise ValueError("early_stop must be a non-negative integer or None")
        early_stop = int(early_stop)
        if early_stop < 0:
            raise ValueError("early_stop must be a non-negative integer or None")
    if hard_timeout_per_logical is not None:
        hard_timeout_per_logical = float(hard_timeout_per_logical)
        if (
            not math.isfinite(hard_timeout_per_logical)
            or hard_timeout_per_logical <= 0
        ):
            raise ValueError(
                "hard_timeout_per_logical must be a positive finite number"
            )

    n = int(code.num_qudits)
    k = int(code.dimension)
    if k == 0:
        return _compute_distance_milp_legacy(
            code,
            timeout_per_logical=timeout_per_logical,
            total_timeout=total_timeout,
            early_stop=early_stop,
            verbose=verbose,
        )

    hx, hz, lx, lz = get_code_matrices(code)
    direction_definitions: list[dict[str, Any]] = []
    for side, logicals, checks in (("Z", lx, hx), ("X", lz, hz)):
        check_sha = _binary_array_sha256(f"{side}-checks", checks)
        for index in range(k):
            logical_sha = _binary_array_sha256(
                f"{side}-logical-{index}", logicals[index]
            )
            direction_definitions.append({
                "direction_id": f"{side}:{index}",
                "side": side,
                "index": index,
                "check_matrix_sha256": check_sha,
                "logical_sha256": logical_sha,
            })
    direction_by_id = {
        row["direction_id"]: row for row in direction_definitions
    }
    identity = _canonical_json(
        checkpoint_identity
        if checkpoint_identity is not None
        else {"kind": "matrix-bound-css-code", "n": n, "k": k}
    )
    proof_binding = {
        "candidate_identity": identity,
        "n": n,
        "k": k,
        "matrix_bundle_sha256": _matrix_bundle_sha256(hx, hz, lx, lz),
        "directions": direction_definitions,
        "directions_sha256": _canonical_sha256(direction_definitions),
        "implementation": _implementation_fingerprint(),
        "solver": {
            "backend": "scipy.optimize.milp-highs",
            "formulation": "css-logical-parity",
            "formulation_revision": _CSS_FORMULATION_REVISION,
            "objective": "hamming_weight",
            "presolve": True,
        },
    }
    proof_binding["binding_sha256"] = _canonical_sha256(proof_binding)
    run_parameters = {
        "timeout_per_logical_s": _checkpoint_budget(timeout_per_logical),
        "total_timeout_s": _checkpoint_budget(total_timeout),
        "hard_timeout_per_logical_s": hard_timeout_per_logical,
        "early_stop": early_stop,
    }

    path = Path(checkpoint_path) if checkpoint_path is not None else None
    records: dict[str, dict[str, Any]] = {}
    created_at = _utc_now()
    parameter_history: list[dict[str, Any]] = []
    checkpoint_resumed = False
    reused_at_start = 0
    hard_timeout_migration = False
    if path is not None and resume and checkpoint_exists:
        checkpoint = _read_checkpoint_json(path)
        if not isinstance(checkpoint, dict):
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint root must be an object"
            )
        expected_checkpoint_fields = {
            "kind",
            "schema_version",
            "created_at",
            "updated_at",
            "status",
            "proof_binding",
            "run_parameters",
            "parameter_history",
            "direction_results",
        }
        if set(checkpoint) != expected_checkpoint_fields:
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint body fields mismatch"
            )
        if (
            checkpoint.get("kind") != _CSS_CHECKPOINT_KIND
            or checkpoint.get("schema_version") != _CSS_CHECKPOINT_SCHEMA_VERSION
        ):
            raise CssCheckpointIncompatibleError(
                "unsupported CSS MILP checkpoint schema"
            )
        if checkpoint.get("proof_binding") != proof_binding:
            raise CssCheckpointIncompatibleError(
                "CSS MILP checkpoint candidate/matrix/direction binding mismatch"
            )
        previous_parameters = checkpoint.get("run_parameters")
        if not isinstance(previous_parameters, dict):
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint has no bound run parameters"
            )
        if set(previous_parameters) != set(run_parameters):
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint run parameter fields mismatch"
            )
        if previous_parameters.get("early_stop") != early_stop:
            raise CssCheckpointIncompatibleError(
                "CSS MILP checkpoint early_stop binding mismatch"
            )
        for field in (
            "timeout_per_logical_s",
            "total_timeout_s",
        ):
            previous_budget = _validated_checkpoint_budget(
                field, previous_parameters[field]
            )
            if not _is_budget_upgrade(
                previous_budget, run_parameters[field]
            ):
                raise CssCheckpointIncompatibleError(
                    f"CSS MILP checkpoint cannot reduce bound budget {field}"
                )
        previous_hard_timeout = _validated_checkpoint_budget(
            "hard_timeout_per_logical_s",
            previous_parameters["hard_timeout_per_logical_s"],
        )
        current_hard_timeout = run_parameters["hard_timeout_per_logical_s"]
        hard_timeout_migration = (
            previous_hard_timeout is None and current_hard_timeout is not None
        )
        if not hard_timeout_migration and not _is_budget_upgrade(
            previous_hard_timeout, current_hard_timeout
        ):
            raise CssCheckpointIncompatibleError(
                "CSS MILP checkpoint cannot reduce bound budget "
                "hard_timeout_per_logical_s"
            )
        raw_records = checkpoint.get("direction_results", {})
        if not isinstance(raw_records, dict):
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint direction_results must be an object"
            )
        for direction_id, record in raw_records.items():
            definition = direction_by_id.get(direction_id)
            if definition is None or not isinstance(record, dict):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint contains an unknown direction"
                )
            if set(record) != {
                "side",
                "index",
                "logical_sha256",
                "status",
                "weight",
                "witness",
                "optimal",
                "attempts",
                "hard_timeouts",
                "last_attempt_status",
                "last_attempt_elapsed_s",
                "updated_at",
            }:
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint direction record fields mismatch"
                )
            status = record.get("status")
            weight = record.get("weight")
            witness = record.get("witness")
            attempts = record.get("attempts")
            if not isinstance(status, str) or status not in _DIRECTION_STATUSES:
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid direction status"
                )
            if (
                record.get("side") != definition["side"]
                or record.get("index") != definition["index"]
                or record.get("logical_sha256") != definition["logical_sha256"]
            ):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint direction binding mismatch"
                )
            if isinstance(attempts, bool) or not isinstance(attempts, int) or attempts < 1:
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid attempt count"
                )
            if weight is not None and (
                isinstance(weight, bool)
                or not isinstance(weight, int)
                or weight < 1
                or weight > n
            ):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid direction weight"
                )
            if status in {"optimal", "incumbent"}:
                if weight is None:
                    raise CssCheckpointCorruptionError(
                        "CSS MILP checkpoint lost a feasible direction weight"
                    )
                if definition["side"] == "Z":
                    checks = hx
                    logical = lx[definition["index"]]
                else:
                    checks = hz
                    logical = lz[definition["index"]]
                try:
                    witness = _validate_css_direction_witness(
                        checks, logical, weight, witness
                    )
                except ValueError as exc:
                    raise CssCheckpointCorruptionError(
                        "CSS MILP checkpoint has invalid feasible witness"
                    ) from exc
            elif weight is not None or witness is not None:
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint unresolved direction retained a witness"
                )
            if record.get("optimal") is not (status == "optimal"):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has inconsistent optimal flag"
                )
            hard_timeouts = record.get("hard_timeouts", 0)
            if (
                isinstance(hard_timeouts, bool)
                or not isinstance(hard_timeouts, int)
                or hard_timeouts < 0
                or hard_timeouts > attempts
            ):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid timeout count"
                )
            last_status = record.get("last_attempt_status")
            if (
                not isinstance(last_status, str)
                or last_status not in _DIRECTION_STATUSES
            ):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid last attempt status"
                )
            if status == "optimal" and last_status != "optimal":
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint optimal record is inconsistent"
                )
            if status in {"no_incumbent", "hard_timeout"} and last_status != status:
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint unresolved record is inconsistent"
                )
            if status == "incumbent" and last_status == "optimal":
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint incumbent record is inconsistent"
                )
            if last_status == "hard_timeout" and hard_timeouts < 1:
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint lost its hard timeout count"
                )
            last_elapsed = record.get("last_attempt_elapsed_s")
            if (
                isinstance(last_elapsed, bool)
                or not isinstance(last_elapsed, (int, float))
                or not math.isfinite(last_elapsed)
                or last_elapsed < 0
            ):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid attempt elapsed time"
                )
            updated_at = record.get("updated_at")
            if not isinstance(updated_at, str) or not updated_at:
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid update timestamp"
                )
            restored = dict(record)
            restored["weight"] = weight
            restored["witness"] = witness
            if hard_timeout_migration and status != "optimal":
                continue
            records[direction_id] = restored
        checkpoint_status = checkpoint.get("status")
        if (
            not isinstance(checkpoint_status, str)
            or checkpoint_status
            not in {
                "running",
                "exact",
                "threshold_rejected",
                "unresolved",
            }
        ):
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint has invalid aggregate status"
            )
        for timestamp_field in ("created_at", "updated_at"):
            timestamp = checkpoint.get(timestamp_field)
            if not isinstance(timestamp, str) or not timestamp:
                raise CssCheckpointCorruptionError(
                    f"CSS MILP checkpoint has invalid {timestamp_field}"
                )
        created_at = checkpoint["created_at"]
        raw_history = checkpoint.get("parameter_history", [])
        if not isinstance(raw_history, list) or not raw_history:
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint parameter history must be non-empty"
            )
        for history_entry in raw_history:
            if (
                not isinstance(history_entry, dict)
                or set(history_entry) != set(run_parameters)
                or history_entry.get("early_stop") != early_stop
            ):
                raise CssCheckpointCorruptionError(
                    "CSS MILP checkpoint has invalid parameter history"
                )
            for field in (
                "timeout_per_logical_s",
                "total_timeout_s",
                "hard_timeout_per_logical_s",
            ):
                _validated_checkpoint_budget(field, history_entry[field])
        if raw_history[-1] != previous_parameters:
            raise CssCheckpointCorruptionError(
                "CSS MILP checkpoint parameter history is not current"
            )
        parameter_history = list(raw_history)
        checkpoint_resumed = True
        reused_at_start = sum(
            record.get("status") == "optimal" for record in records.values()
        )

    if not parameter_history or parameter_history[-1] != run_parameters:
        parameter_history.append(run_parameters)

    def save_checkpoint(status: str) -> None:
        if path is None:
            return
        _atomic_write_json(path, {
            "kind": _CSS_CHECKPOINT_KIND,
            "schema_version": _CSS_CHECKPOINT_SCHEMA_VERSION,
            "created_at": created_at,
            "updated_at": _utc_now(),
            "status": status,
            "proof_binding": proof_binding,
            "run_parameters": run_parameters,
            "parameter_history": parameter_history,
            "direction_results": records,
        })

    save_checkpoint("running")
    t_start = time.monotonic()
    runner = (
        _HardWallCssDirectionSolver(hx, hz, lx, lz)
        if hard_timeout_per_logical is not None
        else None
    )

    def remaining() -> float:
        return max(0.0, total_timeout - (time.monotonic() - t_start))

    def aggregate() -> dict[str, Any]:
        z_weights = [
            int(record["weight"])
            for direction_id, record in records.items()
            if direction_id.startswith("Z:") and record.get("weight") is not None
        ]
        x_weights = [
            int(record["weight"])
            for direction_id, record in records.items()
            if direction_id.startswith("X:") and record.get("weight") is not None
        ]
        feasible = []
        for record in records.values():
            if record.get("weight") is None:
                continue
            witness = record.get("witness")
            if witness is None:
                raise RuntimeError(
                    "CSS MILP feasible direction lost its embedded witness"
                )
            side = record["side"]
            index = int(record["index"])
            weight = int(record["weight"])
            feasible.append((
                weight,
                0 if side == "Z" else 1,
                index,
                {
                    "side": side,
                    "index": index,
                    "weight": weight,
                    "bits": list(witness),
                },
            ))
        minimum_witness = (
            min(feasible, key=lambda item: item[:3])[-1] if feasible else None
        )
        statuses = {
            name: sum(record.get("status") == name for record in records.values())
            for name in sorted(_DIRECTION_STATUSES)
        }
        optimal = statuses["optimal"]
        exact = optimal == 2 * k and len(records) == 2 * k
        pending = [
            definition["direction_id"]
            for definition in direction_definitions
            if records.get(definition["direction_id"], {}).get("status") != "optimal"
        ]
        return {
            "z_weights": z_weights,
            "x_weights": x_weights,
            "d_z": min(z_weights) if z_weights else n,
            "d_x": min(x_weights) if x_weights else n,
            "any_z": bool(z_weights),
            "any_x": bool(x_weights),
            "exact": exact,
            "checked": len(records),
            "optimal": optimal,
            "incumbent": sum(
                record.get("status") == "incumbent"
                for record in records.values()
            ),
            "hard_timeouts": sum(
                int(record.get("hard_timeouts", 0) or 0)
                for record in records.values()
            ),
            "total_attempts": sum(
                int(record.get("attempts", 0) or 0)
                for record in records.values()
            ),
            "statuses": statuses,
            "pending": pending,
            "minimum_direction_witness": minimum_witness,
        }

    def finish(status: str, *, d_x_computed: bool) -> tuple[int, dict]:
        summary = aggregate()
        exact = bool(summary["exact"])
        checkpoint_status = "exact" if exact else status
        save_checkpoint(checkpoint_status)
        elapsed = time.monotonic() - t_start
        details = {
            "d_x": summary["d_x"] if summary["any_x"] else 0,
            "d_z": summary["d_z"] if summary["any_z"] else 0,
            "k": k,
            "exact": exact,
            "d_x_computed": d_x_computed,
            "num_logicals_checked": summary["checked"],
            "logicals_optimal": summary["optimal"],
            "logicals_incumbent": summary["incumbent"],
            "total_logicals": 2 * k,
            "time_s": elapsed,
            "timeout_per_logical": timeout_per_logical,
            "hard_timeout_per_logical": hard_timeout_per_logical,
            "hard_wall_timeouts": summary["hard_timeouts"],
            "total_direction_attempts": summary["total_attempts"],
            "direction_status_counts": summary["statuses"],
            "pending_direction_ids": summary["pending"],
            "checkpoint_enabled": path is not None,
            "checkpoint_path": str(path) if path is not None else None,
            "checkpoint_resumed": checkpoint_resumed,
            "checkpoint_directions_reused": reused_at_start,
            "checkpoint_status": checkpoint_status,
            "minimum_direction_witness": summary["minimum_direction_witness"],
        }
        if not summary["any_z"] and not summary["any_x"]:
            details.update({
                "all_timeout": True,
                "no_incumbent": True,
                "distance_status": "unknown",
                "d_is_lower_bound": False,
            })
            return n, details
        return min(summary["d_z"], summary["d_x"]), details

    def threshold_reached(summary: dict[str, Any]) -> bool:
        if early_stop is None:
            return False
        weights = summary["z_weights"] + summary["x_weights"]
        return bool(weights) and min(weights) <= early_stop

    def record_attempt(
        definition: dict[str, Any],
        weight: int | None,
        optimal: bool,
        outcome: str,
        witness: list[int] | None,
        elapsed: float,
    ) -> None:
        direction_id = definition["direction_id"]
        previous = records.get(direction_id, {})
        previous_weight = previous.get("weight")
        previous_witness = previous.get("witness")
        if outcome not in _DIRECTION_STATUSES:
            raise RuntimeError("CSS MILP direction returned an invalid status")
        if not isinstance(optimal, (bool, np.bool_)):
            raise RuntimeError("CSS MILP direction returned an invalid optimal flag")
        optimal = bool(optimal)
        if (
            isinstance(elapsed, bool)
            or not isinstance(elapsed, (int, float))
            or not math.isfinite(elapsed)
            or elapsed < 0
        ):
            raise RuntimeError("CSS MILP direction returned an invalid elapsed time")
        if weight is not None and (
            isinstance(weight, bool)
            or int(weight) != weight
            or not 1 <= int(weight) <= n
        ):
            raise RuntimeError("CSS MILP direction returned an invalid weight")
        if weight is not None:
            weight = int(weight)
            if definition["side"] == "Z":
                checks = hx
                logical = lx[definition["index"]]
            else:
                checks = hz
                logical = lz[definition["index"]]
            try:
                witness = _validate_css_direction_witness(
                    checks, logical, weight, witness
                )
            except ValueError as exc:
                raise RuntimeError(
                    "CSS MILP direction returned an invalid feasible witness"
                ) from exc
        elif witness is not None:
            raise RuntimeError("CSS MILP direction returned witness without weight")
        expected_outcomes = (
            {"optimal"}
            if optimal
            else {"incumbent"}
            if weight is not None
            else {"no_incumbent", "hard_timeout"}
        )
        if outcome not in expected_outcomes:
            raise RuntimeError("CSS MILP direction result fields are inconsistent")
        if optimal and weight is None:
            raise RuntimeError("optimal CSS MILP direction had no feasible weight")
        if optimal and previous_weight is not None and weight > previous_weight:
            raise RuntimeError("optimal CSS MILP result exceeds prior feasible incumbent")
        if weight is not None and (
            previous_weight is None or weight < previous_weight
        ):
            best_weight = weight
            best_witness = witness
        else:
            best_weight = previous_weight
            best_witness = previous_witness
        if optimal:
            status = "optimal"
            best_weight = weight
            best_witness = witness
        elif best_weight is not None:
            status = "incumbent"
        else:
            status = outcome
            best_weight = None
            best_witness = None
        records[direction_id] = {
            "side": definition["side"],
            "index": definition["index"],
            "logical_sha256": definition["logical_sha256"],
            "status": status,
            "weight": best_weight,
            "witness": best_witness,
            "optimal": status == "optimal",
            "attempts": int(previous.get("attempts", 0) or 0) + 1,
            "hard_timeouts": int(previous.get("hard_timeouts", 0) or 0)
            + int(outcome == "hard_timeout"),
            "last_attempt_status": outcome,
            "last_attempt_elapsed_s": elapsed,
            "updated_at": _utc_now(),
        }
        save_checkpoint("running")

    try:
        x_phase_started = any(
            direction_id.startswith("X:") for direction_id in records
        )
        initial = aggregate()
        if initial["exact"]:
            return finish("exact", d_x_computed=True)
        if threshold_reached(initial):
            return finish(
                "threshold_rejected",
                d_x_computed=x_phase_started,
            )

        for definition in direction_definitions:
            direction_id = definition["direction_id"]
            if records.get(direction_id, {}).get("status") == "optimal":
                continue
            budget = remaining()
            if budget <= 0:
                break
            if definition["side"] == "X":
                x_phase_started = True
            soft_timeout = min(timeout_per_logical, budget)
            started = time.monotonic()
            if runner is None:
                if definition["side"] == "Z":
                    weight, optimal, witness = ilp_min_weight(
                        hx,
                        lx[definition["index"]],
                        timeout=soft_timeout,
                        return_witness=True,
                    )
                else:
                    weight, optimal, witness = ilp_min_weight(
                        hz,
                        lz[definition["index"]],
                        timeout=soft_timeout,
                        return_witness=True,
                    )
                outcome = (
                    "optimal" if optimal
                    else "incumbent" if weight is not None
                    else "no_incumbent"
                )
            else:
                hard_timeout = min(hard_timeout_per_logical, budget)
                weight, optimal, outcome, witness = runner.solve(
                    definition["side"],
                    definition["index"],
                    soft_timeout=soft_timeout,
                    hard_timeout=hard_timeout,
                )
            direction_elapsed = time.monotonic() - started
            record_attempt(
                definition, weight, optimal, outcome, witness, direction_elapsed
            )
            if verbose:
                logger.info(
                    "%s[%d]: d=%s status=%s (%.1fs)",
                    definition["side"],
                    definition["index"],
                    weight,
                    outcome,
                    time.monotonic() - t_start,
                )
            summary = aggregate()
            if threshold_reached(summary):
                return finish(
                    "threshold_rejected",
                    d_x_computed=x_phase_started,
                )

        final = aggregate()
        return finish(
            "exact" if final["exact"] else "unresolved",
            d_x_computed=x_phase_started,
        )
    finally:
        if runner is not None:
            runner.close()


def compute_distance_milp(
    code,
    *,
    timeout_per_logical: int = 30,
    total_timeout: int = 120,
    early_stop: int | None = 4,
    verbose: bool = False,
    checkpoint_path: str | Path | None = None,
    resume: bool = True,
    hard_timeout_per_logical: float | None = None,
    checkpoint_identity: Mapping[str, Any] | str | None = None,
    reset_incompatible_checkpoint: bool = False,
) -> tuple[int, dict]:
    """Compute CSS distance, optionally with durable and killable directions.

    The legacy in-process path remains the default. Supplying a checkpoint path
    enables atomic per-direction persistence; supplying a hard timeout runs
    HiGHS in a reusable spawned child that is terminated on deadline. Resuming
    reuses only proven-optimal directions and retries unresolved directions.
    Timeout budgets may increase across resumes, while proof bindings and
    ``early_stop`` must remain identical.
    """
    if checkpoint_path is None and hard_timeout_per_logical is None:
        return _compute_distance_milp_legacy(
            code,
            timeout_per_logical=timeout_per_logical,
            total_timeout=total_timeout,
            early_stop=early_stop,
            verbose=verbose,
        )
    return _compute_distance_milp_durable(
        code,
        timeout_per_logical=timeout_per_logical,
        total_timeout=total_timeout,
        early_stop=early_stop,
        verbose=verbose,
        checkpoint_path=checkpoint_path,
        resume=resume,
        hard_timeout_per_logical=hard_timeout_per_logical,
        checkpoint_identity=checkpoint_identity,
        reset_incompatible_checkpoint=reset_incompatible_checkpoint,
    )


# ---------------------------------------------------------------------------
# Non-CSS (symplectic) MILP formulation
# ---------------------------------------------------------------------------


def ilp_min_weight_symplectic(stabilizer_matrix, logical_op, timeout=30):
    """Find minimum symplectic-weight Pauli in the coset logical_op + stabilizers.

    Uses the symplectic ILP of Landahl, Anderson, and Rice (arXiv:1108.5738,
    2011) with the standard linear encoding of the per-qubit binary OR
    (w_j = x_j OR z_j) via w_j >= x_j and w_j >= z_j; the upper-bound
    constraint w_j <= x_j + z_j is omitted because the minimization objective
    drives w_j down to max(x_j, z_j) on its own. (Note: this is the convex-hull
    description of binary OR, not McCormick relaxation -- McCormick envelopes
    apply to bilinear products of continuous variables.)

    For non-CSS codes, each Pauli operator is (x_1..x_n, z_1..z_n) and its
    symplectic weight is the number of qubits i where x_i OR z_i is nonzero.

    Variables:
      - x_j, z_j: binary, the Pauli operator on qubit j  (2n vars)
      - w_j: binary, 1 if qubit j has nontrivial support   (n vars)
      - s_r: integer slack for mod-2 commutation constraints (num_stabs vars)
      - t:   integer slack for the anticommutation constraint (1 var)

    Objective: minimize sum(w_j)

    Constraints:
      - w_j >= x_j  and  w_j >= z_j  (symplectic weight linearization)
      - For each stabilizer s: sum_j(s_xj * z_j + s_zj * x_j) - 2*s_r = 0
        (commutation, mod-2 encoded via integer slack)
      - For the target logical L: sum_j(L_xj * z_j + L_zj * x_j) - 2*t = 1
        (anticommutation)

    Args:
        stabilizer_matrix: (num_stabs, 2n) binary symplectic matrix.
        logical_op: (2n,) binary vector of a logical operator.
        timeout: solver time limit in seconds.

    Returns:
        (weight, optimal) tuple.  Returns (None, False) if no feasible
        solution found.
    """
    num_stabs, two_n = stabilizer_matrix.shape
    n = two_n // 2

    # Variable layout: [x_0..x_{n-1}, z_0..z_{n-1}, w_0..w_{n-1},
    #                   s_0..s_{num_stabs-1}, t]
    num_vars = 2 * n + n + num_stabs + 1
    idx_x = slice(0, n)
    idx_z = slice(n, 2 * n)
    idx_w = slice(2 * n, 3 * n)
    # Stabilizer slack vars (s_0..s_{num_stabs-1}) live at indices
    # [3n, 3n + num_stabs); they are indexed directly below.
    idx_t = 3 * n + num_stabs

    # Objective: minimize sum(w_j)
    c = np.zeros(num_vars)
    c[idx_w] = 1.0

    # Sparse block model. The dense predecessor materialized two copies of a
    # mostly-zero matrix for every logical direction, which amplified memory
    # pressure under the deep verifier's process pool.
    identity_n = eye(n, format="csr")
    zero_n = csr_matrix((n, n), dtype=float)
    zero_n_slack = csr_matrix((n, num_stabs), dtype=float)
    zero_n_t = csr_matrix((n, 1), dtype=float)
    weight_x_rows = hstack((
        -identity_n, zero_n, identity_n, zero_n_slack, zero_n_t,
    ), format="csr")
    weight_z_rows = hstack((
        zero_n, -identity_n, identity_n, zero_n_slack, zero_n_t,
    ), format="csr")

    stabilizer_x = csr_matrix(stabilizer_matrix[:, :n], dtype=float)
    stabilizer_z = csr_matrix(stabilizer_matrix[:, n:], dtype=float)
    stabilizer_rows = hstack((
        stabilizer_z,
        stabilizer_x,
        csr_matrix((num_stabs, n), dtype=float),
        -2.0 * eye(num_stabs, format="csr"),
        csr_matrix((num_stabs, 1), dtype=float),
    ), format="csr")

    logical_x = csr_matrix(
        np.asarray(logical_op[:n], dtype=float).reshape(1, n)
    )
    logical_z = csr_matrix(
        np.asarray(logical_op[n:], dtype=float).reshape(1, n)
    )
    logical_row = hstack((
        logical_z, logical_x, csr_matrix((1, n), dtype=float),
        csr_matrix((1, num_stabs), dtype=float), csr_matrix([[-2.0]]),
    ), format="csr")

    constraint_matrix = vstack((
        weight_x_rows, weight_z_rows, stabilizer_rows, logical_row,
    ), format="csr")
    row_lb = np.concatenate((np.zeros(2 * n + num_stabs), [1.0]))
    row_ub = np.concatenate((
        np.full(2 * n, np.inf), np.zeros(num_stabs), [1.0],
    ))
    constraints = LinearConstraint(constraint_matrix, row_lb, row_ub)

    # Bounds
    lb = np.zeros(num_vars)
    ub = np.ones(num_vars)
    # Slack vars for stabilizer commutation: s_r can be up to ceil(weight/2)
    for r in range(num_stabs):
        ub[3 * n + r] = np.ceil(np.sum(stabilizer_matrix[r]) / 2)
    # Slack for anticommutation
    ub[idx_t] = np.ceil(np.sum(logical_op) / 2)

    bounds = Bounds(lb, ub)
    integrality = np.ones(num_vars)

    opts = {"presolve": True}
    if 0 < timeout < 1e9:
        opts["time_limit"] = timeout

    result = milp(
        c=c,
        constraints=constraints,
        integrality=integrality,
        bounds=bounds,
        options=opts,
    )

    if result.x is not None:
        w = int(round(result.fun))
        return w, result.success
    return None, False


def compute_distance_milp_symplectic(
    code,
    *,
    timeout_per_logical: int = 30,
    total_timeout: int = 120,
    early_stop: int | None = 4,
    verbose: bool = False,
) -> tuple[int, dict]:
    """Compute code distance via symplectic MILP for non-CSS codes.

    Unlike the CSS version which separates d_X and d_Z, this formulation
    works with the full symplectic representation and minimizes symplectic
    weight directly.

    Args:
        code: A qubit stabilizer code, non-CSS (qldpc's ``QuditCode``).
        timeout_per_logical: Max seconds per individual ILP solve.
        total_timeout: Max total seconds for the entire computation.
        early_stop: Stop immediately when d <= this value. Pass ``None`` to
            disable early stopping and iterate over every logical (required
            when the goal is to certify an exact distance).
        verbose: Log progress.

    Returns:
        (d, details) where d is the distance (or best upper bound on
        timeout) and details dict.
    """
    if timeout_per_logical <= 0:
        timeout_per_logical = float("inf")
    if total_timeout <= 0:
        total_timeout = float("inf")

    n = code.num_qudits
    k = code.dimension
    if k == 0:
        return n, {"k": 0, "exact": True, "num_logicals_checked": 0,
                    "total_logicals": 0, "time_s": 0.0}

    # Get stabilizer matrix and logical operators
    # Use our own GF(2) computation for logicals -- qldpc's get_logical_ops()
    # has bugs for some non-CSS codes (singular matrix errors).
    from evaluation.pbb_code import get_symplectic_logicals
    stab_matrix = np.array(code.matrix, dtype=int) % 2
    logicals = get_symplectic_logicals(code)
    num_logicals = logicals.shape[0]  # 2k logicals

    t_start = time.monotonic()
    logicals_checked = 0
    logicals_optimal = 0
    logicals_incumbent = 0
    all_solved = True
    d_best = n
    any_found = False

    def _remaining():
        return max(0, total_timeout - (time.monotonic() - t_start))

    for i in range(num_logicals):
        remaining = _remaining()
        if remaining <= 0:
            all_solved = False
            break
        timeout = min(timeout_per_logical, remaining)
        w, optimal = ilp_min_weight_symplectic(stab_matrix, logicals[i],
                                                timeout=timeout)
        logicals_checked += 1
        if w is not None:
            d_best = min(d_best, w)
            any_found = True
            if optimal:
                logicals_optimal += 1
            else:
                logicals_incumbent += 1
                all_solved = False
            if verbose:
                tag = "" if optimal else " (incumbent)"
                logger.info("L[%d]: d=%d%s (%.1fs)", i, w, tag,
                            time.monotonic() - t_start)
        else:
            all_solved = False
            if verbose:
                logger.info("L[%d]: no solution (%.1fs)", i,
                            time.monotonic() - t_start)
        if early_stop is not None and any_found and d_best <= early_stop:
            if i + 1 < num_logicals:
                all_solved = False
            break

    elapsed = time.monotonic() - t_start

    if not any_found:
        # Preserve n as the legacy "MILP did not work" sentinel, but attach no
        # mathematical bound to it. A timeout without an incumbent is unknown.
        return n, {
            "k": k,
            "exact": False,
            "num_logicals_checked": logicals_checked,
            "logicals_optimal": logicals_optimal,
            "logicals_incumbent": logicals_incumbent,
            "total_logicals": num_logicals,
            "time_s": elapsed,
            "timeout_per_logical": timeout_per_logical,
            "all_timeout": True,
            "no_incumbent": True,
            "distance_status": "unknown",
            "d_is_lower_bound": False,
        }

    return d_best, {
        "k": k,
        "exact": all_solved and logicals_checked == logicals_optimal == num_logicals,
        "num_logicals_checked": logicals_checked,
        "logicals_optimal": logicals_optimal,
        "logicals_incumbent": logicals_incumbent,
        "total_logicals": num_logicals,
        "time_s": elapsed,
        "timeout_per_logical": timeout_per_logical,
    }
