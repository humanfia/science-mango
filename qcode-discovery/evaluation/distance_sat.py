"""Optional exact CSS distance decisions using a CNF SAT backend.

For one CSS logical sector this module decides whether there is a binary
operator ``x`` satisfying all three conditions

``H x = 0 (mod 2)``, ``L x != 0 (mod 2)``, and ``weight(x) <= max_weight``.

Consequently, an UNSAT decision is a certified lower-bound statement for the
whole sector, rather than a collection of overlapping logical-basis probes.
A SAT decision contains an operator which is replayed algebraically without
trusting any SAT metadata.  The SAT dependency is deliberately optional: the
normal qcode installation can import this module without python-sat, while
``qcode-discovery[sat]`` enables the backend.

The solver runs in a spawned child process.  The parent enforces a hard wall
timeout and kills the child before returning ``hard_timeout``.  Terminal SAT
and UNSAT decisions can be stored as one atomic, identity-bound checkpoint;
timeouts and errors are never reused.

This module does not claim that a bare solver UNSAT string is independently
checkable proof logging.  A publication certificate should either rerun the
decision under its pinned proof runtime or add a solver-specific DRAT/LRAT
artifact and checker as a separate layer.
"""

from __future__ import annotations

import hashlib
import importlib.metadata
import importlib.util
import json
import math
import multiprocessing
import os
import signal
import sys
import time
import traceback
from ctypes import CDLL, c_int, c_ulong, get_errno
from pathlib import Path
from typing import Any, Literal, Mapping, Sequence

import numpy as np


SAT_EVIDENCE_KIND = "qcode-css-threshold-sat-evidence"
SAT_EVIDENCE_SCHEMA_VERSION = 1
SAT_FORMULATION = "css-global-logical-threshold-cnf-v1"
SAT_ENCODINGS = frozenset({
    "kmtotalizer",
    "native-minicard",
    "seqcounter",
    "totalizer",
})
SAT_TERMINAL_OUTCOMES = frozenset({"sat", "unsat"})
SAT_RETRYABLE_OUTCOMES = frozenset({
    "backend_unavailable",
    "cancelled",
    "hard_timeout",
    "solver_error",
    "worker_exit",
})
SAT_NATIVE_THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
    "NUMBA_NUM_THREADS",
)
_AUTO_SOLVERS = (
    "cadical195",
    "cadical300",
    "kissat404",
    "cadical153",
    "glucose42",
    "glucose4",
    "minisat22",
)
# Public, ordered solver list used by the Stage-3 retry portfolio.  The order
# is part of scheduling policy, not mathematical evidence: every terminal
# result remains bound to the concrete selected backend in ``instance``.
SAT_AUTO_SOLVERS = _AUTO_SOLVERS
_FORMULATION_REVISION = "xor-chain-global-or-pysat-cardinality-v1"
_ANCHOR_CUBE_FORMULATION = "anchor-or-first-nonzero-unit-clauses-v1"
# The first deployed sector-SAT campaign wrote two useful weight-24 terminal
# witnesses with this source binding.  Runtime-only cancellation/portfolio
# changes do not alter its CNF formulation.  Keep the exact old digest as an
# explicit compatibility allow-list so those checkpoints are replayed rather
# than silently discarded; no arbitrary historical source is accepted.
_COMPATIBLE_SOURCE_SHA256 = frozenset({
    "f30a0f016fff8a358bb5d387c510e26053f3b500502162dbb0b7d4a9c3be0553",
})
try:
    _SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
except OSError:
    _SOURCE_SHA256 = None


class SatBackendUnavailable(RuntimeError):
    """python-sat, its requested encoding, or a SAT engine is unavailable."""


def enforce_sat_native_thread_budget() -> dict[str, str]:
    """Keep each SAT proof process within one native numeric thread.

    Stage 3 parallelizes across independent proof units.  NumPy/BLAS may
    otherwise create a machine-sized thread pool in every spawned worker,
    turning 12 requested solvers into more than a thousand runnable threads.
    The setting is persistent and idempotent so concurrent Stage-3 threads
    cannot race while spawning their solver children.
    """

    for variable in SAT_NATIVE_THREAD_ENV:
        os.environ[variable] = "1"
    return {variable: os.environ[variable] for variable in SAT_NATIVE_THREAD_ENV}


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
        raise ValueError("SAT identity must be strict JSON data") from exc
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


def _array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode())
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _package_version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def pysat_available() -> bool:
    """Return whether the optional python-sat top-level package is importable."""
    try:
        return importlib.util.find_spec("pysat") is not None
    except (ImportError, ModuleNotFoundError, ValueError):
        return False


def _require_pysat() -> None:
    if not pysat_available():
        raise SatBackendUnavailable(
            "python-sat is not installed; install qcode-discovery[sat]"
        )


def _validated_problem(
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    cardinality_encoding: str,
) -> tuple[np.ndarray, np.ndarray, int, str, str]:
    checks = np.asarray(check_matrix, dtype=np.uint8) & 1
    logicals = np.asarray(target_logicals, dtype=np.uint8) & 1
    if checks.ndim != 2 or logicals.ndim != 2:
        raise ValueError("check_matrix and target_logicals must be matrices")
    if checks.shape[1] <= 0 or logicals.shape[1] != checks.shape[1]:
        raise ValueError("logical/check width mismatch or empty block length")
    if logicals.shape[0] <= 0:
        raise ValueError("target_logicals must contain a nonempty logical basis")
    if isinstance(max_weight, bool) or not isinstance(max_weight, (int, np.integer)):
        raise ValueError("max_weight must be an integer")
    threshold = int(max_weight)
    if threshold < 0:
        raise ValueError("max_weight must be nonnegative")
    normalized_sector = str(sector).upper()
    if normalized_sector not in {"X", "Z"}:
        raise ValueError("sector must be 'X' or 'Z'")
    encoding = str(cardinality_encoding).lower()
    if encoding not in SAT_ENCODINGS:
        raise ValueError(
            "cardinality_encoding must be kmtotalizer, native-minicard, "
            "seqcounter, or totalizer"
        )
    return checks, logicals, threshold, normalized_sector, encoding


def _anchor_cube_record(
    anchor_indices: Sequence[int],
    cube_index: int,
) -> dict[str, Any]:
    """Return the canonical first-nonzero cube inside one anchor OR."""

    anchors = tuple(int(index) for index in anchor_indices)
    required_one = anchors[int(cube_index)]
    cube: dict[str, Any] = {
        "schema_version": 1,
        "cover": "anchor-or-first-nonzero-v1",
        "cube_index": int(cube_index),
        "zero_anchor_indices": list(anchors[: int(cube_index)]),
        "one_anchor_index": required_one,
        "anchor_indices": list(anchors),
    }
    cube["cube_sha256"] = _canonical_sha256(cube)
    return cube


def _validated_partition_and_anchors(
    *,
    num_logicals: int,
    n: int,
    partition_index: int | None,
    anchor_indices: Sequence[int] | None,
    zero_anchor_indices: Sequence[int] | None = None,
    one_anchor_index: int | None = None,
    anchor_cube_sha256: str | None = None,
) -> tuple[int | None, tuple[int, ...], tuple[int, ...], int | None, str | None]:
    if partition_index is None:
        partition = None
    else:
        if (
            isinstance(partition_index, bool)
            or not isinstance(partition_index, (int, np.integer))
        ):
            raise ValueError("partition_index must be an integer or None")
        partition = int(partition_index)
        if not 0 <= partition < num_logicals:
            raise ValueError("partition_index is outside the logical basis")
    anchors: list[int] = []
    for raw_index in anchor_indices or ():
        if isinstance(raw_index, bool) or not isinstance(raw_index, (int, np.integer)):
            raise ValueError("anchor_indices must contain integers")
        index = int(raw_index)
        if not 0 <= index < n:
            raise ValueError("anchor index out of range")
        anchors.append(index)
    if len(set(anchors)) != len(anchors):
        raise ValueError("anchor_indices must be distinct")
    zeros: list[int] = []
    for raw_index in zero_anchor_indices or ():
        if isinstance(raw_index, bool) or not isinstance(raw_index, (int, np.integer)):
            raise ValueError("zero_anchor_indices must contain integers")
        index = int(raw_index)
        if not 0 <= index < n:
            raise ValueError("zero anchor index out of range")
        zeros.append(index)
    if len(set(zeros)) != len(zeros):
        raise ValueError("zero_anchor_indices must be distinct")
    cube_requested = bool(zeros) or one_anchor_index is not None or anchor_cube_sha256 is not None
    if not cube_requested:
        return partition, tuple(anchors), (), None, None
    if (
        isinstance(one_anchor_index, bool)
        or not isinstance(one_anchor_index, (int, np.integer))
    ):
        raise ValueError("one_anchor_index must be an integer for an anchor cube")
    required_one = int(one_anchor_index)
    if not 0 <= required_one < n:
        raise ValueError("one anchor index out of range")
    if not isinstance(anchor_cube_sha256, str) or len(anchor_cube_sha256) != 64:
        raise ValueError("anchor_cube_sha256 must be a 64-character digest")
    try:
        bytes.fromhex(anchor_cube_sha256)
    except ValueError as exc:
        raise ValueError("anchor_cube_sha256 must be hexadecimal") from exc
    anchor_tuple = tuple(anchors)
    if not anchor_tuple or required_one not in anchor_tuple:
        raise ValueError("anchor cube one index must belong to anchor_indices")
    cube_index = anchor_tuple.index(required_one)
    if tuple(zeros) != anchor_tuple[:cube_index]:
        raise ValueError(
            "zero_anchor_indices must be the ordered anchor prefix before "
            "one_anchor_index"
        )
    expected_cube = _anchor_cube_record(anchor_tuple, cube_index)
    if anchor_cube_sha256 != expected_cube["cube_sha256"]:
        raise ValueError("anchor cube hash does not match its first-nonzero cube")
    return (
        partition,
        anchor_tuple,
        tuple(zeros),
        required_one,
        anchor_cube_sha256,
    )


class _CnfBuilder:
    """Small DIMACS builder used for parity Tseitin variables."""

    def __init__(self, initial_variables: int):
        self.num_variables = int(initial_variables)
        self.clauses: list[list[int]] = []

    def new_variable(self) -> int:
        self.num_variables += 1
        return self.num_variables

    def add_clause(self, literals: Sequence[int]) -> None:
        clause = [int(literal) for literal in literals]
        if not clause or any(literal == 0 for literal in clause):
            raise ValueError("CNF clauses must be nonempty nonzero literals")
        self.clauses.append(clause)

    def add_xor_output(self, inputs: Sequence[int], output: int) -> None:
        """Encode ``output <-> XOR(inputs)`` with a linear Tseitin chain."""
        variables = [int(variable) for variable in inputs]
        output = int(output)
        if not variables:
            self.add_clause([-output])
            return
        if len(variables) == 1:
            variable = variables[0]
            self.add_clause([-variable, output])
            self.add_clause([variable, -output])
            return
        left = variables[0]
        for index, right in enumerate(variables[1:], start=1):
            result = output if index == len(variables) - 1 else self.new_variable()
            # result <-> left XOR right
            self.add_clause([left, right, -result])
            self.add_clause([-left, -right, -result])
            self.add_clause([left, -right, result])
            self.add_clause([-left, right, result])
            left = result

    def add_even_parity(self, inputs: Sequence[int]) -> None:
        variables = [int(variable) for variable in inputs]
        if not variables:
            return
        parity = self.new_variable()
        self.add_xor_output(variables, parity)
        self.add_clause([-parity])


def _append_cardinality(
    builder: _CnfBuilder,
    variables: Sequence[int],
    *,
    max_weight: int,
    encoding: str,
) -> dict[str, Any] | None:
    if max_weight >= len(variables):
        return None
    if max_weight == 0:
        for variable in variables:
            builder.add_clause([-int(variable)])
        return None
    if encoding == "native-minicard":
        return {
            "literals": [int(variable) for variable in variables],
            "bound": int(max_weight),
        }
    _require_pysat()
    try:
        from pysat.card import CardEnc, EncType
    except (ImportError, ModuleNotFoundError) as exc:
        raise SatBackendUnavailable(
            "python-sat cardinality encoders are unavailable"
        ) from exc
    encoding_type = {
        "seqcounter": EncType.seqcounter,
        "kmtotalizer": EncType.kmtotalizer,
        "totalizer": EncType.totalizer,
    }[encoding]
    encoded = CardEnc.atmost(
        lits=[int(variable) for variable in variables],
        bound=int(max_weight),
        top_id=builder.num_variables,
        encoding=encoding_type,
    )
    builder.num_variables = max(builder.num_variables, int(encoded.nv))
    for clause in encoded.clauses:
        builder.add_clause(clause)
    return None


def build_css_threshold_cnf(
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    max_weight: int,
    sector: Literal["X", "Z"] | str,
    cardinality_encoding: str = "seqcounter",
    partition_index: int | None = None,
    anchor_indices: Sequence[int] | None = None,
    zero_anchor_indices: Sequence[int] | None = None,
    one_anchor_index: int | None = None,
    anchor_cube_sha256: str | None = None,
) -> dict[str, Any]:
    """Build a JSON-friendly CNF for a complete CSS logical sector.

    Operator variables are DIMACS variables ``1..n``.  Check and logical
    parities use linear-size XOR chains; the logical syndrome variables are
    constrained by one global OR clause.
    """
    checks, logicals, threshold, sector, encoding = _validated_problem(
        check_matrix,
        target_logicals,
        max_weight=max_weight,
        sector=sector,
        cardinality_encoding=cardinality_encoding,
    )
    _require_pysat()
    n = int(checks.shape[1])
    partition, anchors, zero_anchors, one_anchor, cube_sha256 = (
        _validated_partition_and_anchors(
            num_logicals=int(logicals.shape[0]),
            n=n,
            partition_index=partition_index,
            anchor_indices=anchor_indices,
            zero_anchor_indices=zero_anchor_indices,
            one_anchor_index=one_anchor_index,
            anchor_cube_sha256=anchor_cube_sha256,
        )
    )
    operator_variables = list(range(1, n + 1))
    builder = _CnfBuilder(n)
    for row in checks:
        builder.add_even_parity(
            [operator_variables[index] for index in np.flatnonzero(row)]
        )
    logical_variables: list[int] = []
    for row in logicals:
        logical_variable = builder.new_variable()
        logical_variables.append(logical_variable)
        builder.add_xor_output(
            [operator_variables[index] for index in np.flatnonzero(row)],
            logical_variable,
        )
    if partition is None:
        builder.add_clause(logical_variables)
    else:
        # These k cases are disjoint and exhaustive for Lx != 0: case p fixes
        # syndrome bits 0..p-1 to zero and bit p to one.
        for index in range(partition):
            builder.add_clause([-logical_variables[index]])
        builder.add_clause([logical_variables[partition]])
    if anchors:
        builder.add_clause([operator_variables[index] for index in anchors])
    anchor_unit_clauses = [
        [-operator_variables[index]] for index in zero_anchors
    ]
    if one_anchor is not None:
        anchor_unit_clauses.append([operator_variables[one_anchor]])
    for clause in anchor_unit_clauses:
        builder.add_clause(clause)
    native_atmost = _append_cardinality(
        builder,
        operator_variables,
        max_weight=threshold,
        encoding=encoding,
    )
    clauses = builder.clauses
    cnf_sha256 = _canonical_sha256({
        "num_variables": builder.num_variables,
        "clauses": clauses,
        "native_atmost": native_atmost,
    })
    return {
        "formulation": SAT_FORMULATION,
        "formulation_revision": _FORMULATION_REVISION,
        "sector": sector,
        "n": n,
        "num_checks": int(checks.shape[0]),
        "num_logicals": int(logicals.shape[0]),
        "max_weight": threshold,
        "cardinality_encoding": encoding,
        "num_variables": builder.num_variables,
        "num_clauses": len(clauses),
        "operator_variables": operator_variables,
        "logical_variables": logical_variables,
        "partition_index": partition,
        "anchor_indices": list(anchors),
        "zero_anchor_indices": list(zero_anchors),
        "one_anchor_index": one_anchor,
        "anchor_cube_sha256": cube_sha256,
        "anchor_unit_clauses": anchor_unit_clauses,
        "anchor_unit_clauses_sha256": _canonical_sha256(anchor_unit_clauses),
        "native_atmost": native_atmost,
        "clauses": clauses,
        "cnf_sha256": cnf_sha256,
    }


def _pack_vector(vector: np.ndarray) -> dict[str, Any]:
    binary = np.asarray(vector, dtype=np.uint8).reshape(-1) & 1
    packed = np.packbits(binary, bitorder="little").tobytes()
    return {
        "length": int(binary.size),
        "weight": int(binary.sum()),
        "packed_hex": packed.hex(),
        "sha256": hashlib.sha256(f"{binary.size}:".encode() + packed).hexdigest(),
    }


def _unpack_vector(record: Mapping[str, Any]) -> np.ndarray:
    try:
        length = int(record["length"])
        packed = bytes.fromhex(str(record["packed_hex"]))
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("invalid packed vector") from exc
    if length < 0:
        raise ValueError("invalid packed vector length")
    vector = np.unpackbits(
        np.frombuffer(packed, dtype=np.uint8), bitorder="little"
    )[:length].astype(np.uint8)
    if _pack_vector(vector) != dict(record):
        raise ValueError("packed vector metadata/hash mismatch")
    return vector


def verify_css_threshold_sat_witness(
    evidence: Mapping[str, Any],
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
) -> list[str]:
    """Replay a SAT operator from matrices, independent of the SAT solver."""
    if evidence.get("outcome") != "sat":
        return ["evidence does not contain a SAT witness"]
    try:
        vector = _unpack_vector(evidence["operator"])
    except (KeyError, TypeError, ValueError) as exc:
        return [f"invalid packed vector: {exc}"]
    checks = np.asarray(check_matrix, dtype=np.uint8) & 1
    logicals = np.asarray(target_logicals, dtype=np.uint8) & 1
    if checks.ndim != 2 or logicals.ndim != 2:
        return ["checks and logicals must be matrices"]
    if vector.size != checks.shape[1] or logicals.shape[1] != vector.size:
        return ["operator width mismatch"]
    failures: list[str] = []
    if np.any((checks @ vector) & 1):
        failures.append("operator has nonzero stabilizer syndrome")
    syndrome = ((logicals @ vector) & 1).astype(int).tolist()
    if not any(syndrome):
        failures.append("operator is trivial in the logical quotient")
    if evidence.get("logical_syndrome") != syndrome:
        failures.append("stored logical syndrome does not match operator")
    partition = evidence.get("partition_index")
    if partition is not None:
        try:
            partition = int(partition)
        except (TypeError, ValueError):
            failures.append("invalid partition index")
        else:
            if (
                not 0 <= partition < len(syndrome)
                or any(syndrome[:partition])
                or syndrome[partition] != 1
            ):
                failures.append("operator violates first-nonzero partition")
    try:
        anchors = [int(index) for index in evidence.get("anchor_indices", [])]
    except (TypeError, ValueError):
        failures.append("invalid anchor indices")
        anchors = []
    if any(index < 0 or index >= vector.size for index in anchors):
        failures.append("anchor index out of range")
    elif anchors and not any(int(vector[index]) for index in anchors):
        failures.append("operator violates stored symmetry anchors")
    try:
        zero_anchors = [
            int(index) for index in evidence.get("zero_anchor_indices", [])
        ]
    except (TypeError, ValueError):
        failures.append("invalid zero anchor indices")
        zero_anchors = []
    raw_one_anchor = evidence.get("one_anchor_index")
    raw_cube_sha256 = evidence.get("anchor_cube_sha256")
    cube_requested = bool(zero_anchors) or raw_one_anchor is not None or raw_cube_sha256 is not None
    if cube_requested:
        try:
            _, _, validated_zeros, one_anchor, cube_sha256 = (
                _validated_partition_and_anchors(
                    num_logicals=int(logicals.shape[0]),
                    n=int(vector.size),
                    partition_index=partition,
                    anchor_indices=anchors,
                    zero_anchor_indices=zero_anchors,
                    one_anchor_index=raw_one_anchor,
                    anchor_cube_sha256=raw_cube_sha256,
                )
            )
        except ValueError as exc:
            failures.append(f"invalid anchor cube: {exc}")
        else:
            if any(int(vector[index]) for index in validated_zeros):
                failures.append("operator violates zero-anchor cube literals")
            if one_anchor is None or int(vector[one_anchor]) != 1:
                failures.append("operator violates one-anchor cube literal")
            if cube_sha256 != raw_cube_sha256:
                failures.append("stored anchor cube hash mismatch")
    weight = int(vector.sum())
    if evidence.get("objective") != weight:
        failures.append("objective does not equal operator weight")
    try:
        threshold = int(evidence["max_weight"])
    except (KeyError, TypeError, ValueError):
        failures.append("invalid max_weight")
    else:
        if weight > threshold:
            failures.append("operator exceeds threshold bound")
    return failures


def css_sector_matrices(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    sector: Literal["X", "Z"] | str,
) -> tuple[np.ndarray, np.ndarray]:
    """Return the commutation checks and dual logicals for one CSS sector."""
    normalized = str(sector).upper()
    if normalized == "Z":
        return np.asarray(hx, dtype=np.uint8) & 1, np.asarray(lx, dtype=np.uint8) & 1
    if normalized == "X":
        return np.asarray(hz, dtype=np.uint8) & 1, np.asarray(lz, dtype=np.uint8) & 1
    raise ValueError("sector must be 'X' or 'Z'")


def _select_solver(requested: str) -> str:
    _require_pysat()
    try:
        from pysat.solvers import NoSuchSolverError, Solver
    except (ImportError, ModuleNotFoundError) as exc:
        raise SatBackendUnavailable("python-sat solvers are unavailable") from exc
    names = _AUTO_SOLVERS if requested == "auto" else (str(requested),)
    failures: list[str] = []
    for name in names:
        try:
            with Solver(name=name):
                return name
        except (NoSuchSolverError, ImportError, RuntimeError, ValueError) as exc:
            failures.append(f"{name}: {type(exc).__name__}")
    raise SatBackendUnavailable(
        "no requested python-sat solver is available (" + ", ".join(failures) + ")"
    )


def _instance_binding(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    encoding: str,
    solver_name: str,
    checkpoint_identity: Mapping[str, Any] | str | None,
    partition_index: int | None,
    anchor_indices: Sequence[int],
    zero_anchor_indices: Sequence[int] = (),
    one_anchor_index: int | None = None,
    anchor_cube_sha256: str | None = None,
) -> dict[str, Any]:
    if _SOURCE_SHA256 is None:
        raise RuntimeError("cannot fingerprint distance_sat.py")
    binding = {
        "formulation": SAT_FORMULATION,
        "formulation_revision": _FORMULATION_REVISION,
        "source_sha256": _SOURCE_SHA256,
        "sector": sector,
        "n": int(checks.shape[1]),
        "num_checks": int(checks.shape[0]),
        "num_logicals": int(logicals.shape[0]),
        "check_matrix_sha256": _array_sha256("checks", checks),
        "target_logicals_sha256": _array_sha256("logicals", logicals),
        "max_weight": int(max_weight),
        "cardinality_encoding": encoding,
        "partition_index": partition_index,
        "anchor_indices": [int(index) for index in anchor_indices],
        "backend": {
            "distribution": "python-sat",
            "version": _package_version("python-sat"),
            "solver": solver_name,
        },
        "checkpoint_identity": (
            None if checkpoint_identity is None else _canonical_json(checkpoint_identity)
        ),
    }
    if anchor_cube_sha256 is not None:
        anchor_unit_clauses = [
            [-(int(index) + 1)] for index in zero_anchor_indices
        ]
        if one_anchor_index is None:
            raise ValueError("anchor cube binding is missing one_anchor_index")
        anchor_unit_clauses.append([int(one_anchor_index) + 1])
        binding.update({
            "anchor_constraint_formulation": _ANCHOR_CUBE_FORMULATION,
            "zero_anchor_indices": [int(index) for index in zero_anchor_indices],
            "one_anchor_index": int(one_anchor_index),
            "anchor_cube_sha256": str(anchor_cube_sha256),
            "anchor_unit_clauses": anchor_unit_clauses,
            "anchor_unit_clauses_sha256": _canonical_sha256(
                anchor_unit_clauses,
            ),
        })
    binding["binding_sha256"] = _canonical_sha256(binding)
    return binding


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{time.time_ns()}.tmp")
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(
                value,
                stream,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
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
        except OSError:
            pass
        finally:
            os.close(directory_fd)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _binding_without_self_hash(binding: Mapping[str, Any]) -> dict[str, Any] | None:
    """Return a binding only after validating its embedded canonical hash."""

    try:
        unsigned = dict(binding)
        stored_hash = unsigned.pop("binding_sha256")
    except (KeyError, TypeError, ValueError):
        return None
    try:
        if stored_hash != _canonical_sha256(unsigned):
            return None
    except (TypeError, ValueError):
        return None
    return unsigned


def _checkpoint_binding_matches(
    stored: Mapping[str, Any],
    current: Mapping[str, Any],
) -> bool:
    """Match current or explicitly allow-listed formulation-equivalent code.

    Source fingerprints normally make checkpoints fail closed after any code
    edit.  For a reviewed runtime-only change we permit a named predecessor
    only when every other instance field, including formulation revision,
    matrices, backend, partition, anchors, and caller identity, is identical.
    """

    stored_unsigned = _binding_without_self_hash(stored)
    current_unsigned = _binding_without_self_hash(current)
    if stored_unsigned is None or current_unsigned is None:
        return False
    if stored_unsigned == current_unsigned:
        return True
    stored_source = stored_unsigned.pop("source_sha256", None)
    current_source = current_unsigned.pop("source_sha256", None)
    if not (
        stored_source in _COMPATIBLE_SOURCE_SHA256
        and current_source == _SOURCE_SHA256
    ):
        return False
    migrated_current = dict(current_unsigned)
    stored_environment = stored_unsigned.get("native_thread_environment")
    current_environment = current_unsigned.get("native_thread_environment")
    if (
        isinstance(stored_environment, Mapping)
        and isinstance(current_environment, Mapping)
        and current_environment.get("NUMBA_NUM_THREADS") == "1"
    ):
        without_numba = dict(current_environment)
        without_numba.pop("NUMBA_NUM_THREADS", None)
        if dict(stored_environment) == without_numba:
            migrated_current["native_thread_environment"] = without_numba
    if stored_unsigned == migrated_current:
        return True
    # The first campaign predates the explicit BB X/Z-isometry report.  That
    # report changes which sector units the scheduler requires, but not any
    # individual CNF.  Permit exactly the migration from the otherwise equal
    # old caller identity to the new identity containing only this report
    # hash; all matrix/formulation/backend fields above still match exactly.
    stored_identity = stored_unsigned.get("checkpoint_identity")
    current_identity = migrated_current.get("checkpoint_identity")
    if not (
        isinstance(stored_identity, Mapping)
        and isinstance(current_identity, Mapping)
    ):
        return False
    migrated_identity = dict(current_identity)
    isometry_hash = migrated_identity.pop("xz_sector_isometry_sha256", None)
    if not isinstance(isometry_hash, str) or len(isometry_hash) != 64:
        return False
    migrated_binding = dict(migrated_current)
    migrated_binding["checkpoint_identity"] = migrated_identity
    return stored_unsigned == migrated_binding


def _load_terminal_checkpoint(
    path: Path,
    *,
    binding: Mapping[str, Any],
    checks: np.ndarray,
    logicals: np.ndarray,
) -> dict[str, Any] | None:
    try:
        with path.open("r", encoding="utf-8") as stream:
            evidence = json.load(stream)
    except (OSError, UnicodeError, json.JSONDecodeError):
        return None
    if not isinstance(evidence, dict):
        return None
    if (
        evidence.get("schema_version") != SAT_EVIDENCE_SCHEMA_VERSION
        or evidence.get("evidence_kind") != SAT_EVIDENCE_KIND
        or not isinstance(evidence.get("instance"), Mapping)
        or not _checkpoint_binding_matches(evidence["instance"], binding)
        or evidence.get("outcome") not in SAT_TERMINAL_OUTCOMES
    ):
        return None
    # A SAT result crosses the one explicitly reviewed runtime-only source
    # migration only because its operator is independently replayed below.
    # Bare UNSAT has no proof object yet, so it must retain an exact current
    # source binding and is never grandfathered by the compatibility allowlist.
    if evidence.get("outcome") == "unsat" and evidence.get("instance") != binding:
        return None
    expected_hash = evidence.get("evidence_sha256")
    unsigned = dict(evidence)
    unsigned.pop("evidence_sha256", None)
    if expected_hash != _canonical_sha256(unsigned):
        return None
    if evidence.get("outcome") == "sat" and verify_css_threshold_sat_witness(
        evidence, checks, logicals
    ):
        return None
    resumed = dict(evidence)
    resumed["resumed"] = True
    unsigned = dict(resumed)
    unsigned.pop("evidence_sha256", None)
    resumed["evidence_sha256"] = _canonical_sha256(unsigned)
    return resumed


def _set_parent_death_signal(expected_parent_pid: int) -> None:
    if not sys.platform.startswith("linux"):
        return
    libc = CDLL(None, use_errno=True)
    prctl = libc.prctl
    prctl.restype = c_int
    result = prctl(c_int(1), c_ulong(signal.SIGKILL), 0, 0, 0)
    if result != 0:
        error_number = get_errno()
        raise OSError(error_number, os.strerror(error_number))
    if os.getppid() != expected_parent_pid:
        os.kill(os.getpid(), signal.SIGKILL)


def _solve_inprocess(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    encoding: str,
    solver_name: str,
    partition_index: int | None,
    anchor_indices: Sequence[int],
    zero_anchor_indices: Sequence[int],
    one_anchor_index: int | None,
    anchor_cube_sha256: str | None,
) -> dict[str, Any]:
    from pysat.solvers import Solver

    started = time.monotonic()
    cnf = build_css_threshold_cnf(
        checks,
        logicals,
        max_weight=max_weight,
        sector=sector,
        cardinality_encoding=encoding,
        partition_index=partition_index,
        anchor_indices=anchor_indices,
        zero_anchor_indices=zero_anchor_indices,
        one_anchor_index=one_anchor_index,
        anchor_cube_sha256=anchor_cube_sha256,
    )
    built_s = time.monotonic() - started
    solve_started = time.monotonic()
    with Solver(
        name=solver_name,
        bootstrap_with=cnf["clauses"],
        use_timer=True,
    ) as solver:
        native_atmost = cnf.get("native_atmost")
        if native_atmost is not None:
            if solver_name != "minicard" or not solver.supports_atmost():
                raise SatBackendUnavailable(
                    "native-minicard encoding requires the MiniCard solver"
                )
            solver.add_atmost(
                native_atmost["literals"],
                native_atmost["bound"],
            )
        satisfiable = solver.solve()
        model = solver.get_model() if satisfiable else None
        solver_time = float(solver.time())
    solve_s = time.monotonic() - solve_started
    operator = None
    objective = None
    syndrome = None
    if satisfiable:
        positive = {int(literal) for literal in model or () if int(literal) > 0}
        vector = np.fromiter(
            (int(variable in positive) for variable in cnf["operator_variables"]),
            dtype=np.uint8,
            count=int(cnf["n"]),
        )
        operator = _pack_vector(vector)
        objective = int(vector.sum())
        syndrome = ((logicals @ vector) & 1).astype(int).tolist()
    return {
        "outcome": "sat" if satisfiable else "unsat",
        "decision_complete": True,
        "threshold_infeasible": not satisfiable,
        "success": bool(satisfiable),
        "operator": operator,
        "objective": objective,
        "logical_syndrome": syndrome,
        "partition_index": partition_index,
        "anchor_indices": [int(index) for index in anchor_indices],
        "zero_anchor_indices": [int(index) for index in zero_anchor_indices],
        "one_anchor_index": one_anchor_index,
        "anchor_cube_sha256": anchor_cube_sha256,
        "cnf": {
            key: cnf[key]
            for key in (
                "num_variables",
                "num_clauses",
                "cnf_sha256",
                "cardinality_encoding",
                "anchor_unit_clauses_sha256",
            )
        },
        "build_time_s": built_s,
        "solve_time_s": solve_s,
        "solver_reported_time_s": solver_time,
        "elapsed_s": time.monotonic() - started,
    }


def _solver_worker(
    connection,
    expected_parent_pid: int,
    checks: np.ndarray,
    logicals: np.ndarray,
    max_weight: int,
    sector: str,
    encoding: str,
    solver_name: str,
    partition_index: int | None,
    anchor_indices: Sequence[int],
    zero_anchor_indices: Sequence[int],
    one_anchor_index: int | None,
    anchor_cube_sha256: str | None,
) -> None:
    try:
        _set_parent_death_signal(expected_parent_pid)
        result = _solve_inprocess(
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
            encoding=encoding,
            solver_name=solver_name,
            partition_index=partition_index,
            anchor_indices=anchor_indices,
            zero_anchor_indices=zero_anchor_indices,
            one_anchor_index=one_anchor_index,
            anchor_cube_sha256=anchor_cube_sha256,
        )
        connection.send(("result", result))
    except BaseException as exc:
        try:
            connection.send((
                "error",
                type(exc).__name__,
                str(exc),
                traceback.format_exc(),
            ))
        except (BrokenPipeError, EOFError, OSError):
            pass
    finally:
        connection.close()


def _base_evidence(
    *,
    binding: Mapping[str, Any],
    hard_timeout_s: float,
) -> dict[str, Any]:
    return {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "formulation": SAT_FORMULATION,
        "instance": dict(binding),
        "sector": binding["sector"],
        "max_weight": binding["max_weight"],
        "cardinality_encoding": binding["cardinality_encoding"],
        "backend": binding["backend"],
        "partition_index": binding.get("partition_index"),
        "anchor_indices": list(binding.get("anchor_indices", [])),
        "zero_anchor_indices": list(binding.get("zero_anchor_indices", [])),
        "one_anchor_index": binding.get("one_anchor_index"),
        "anchor_cube_sha256": binding.get("anchor_cube_sha256"),
        "hard_timeout_s": hard_timeout_s,
        "resumed": False,
    }


def _seal_evidence(result: dict[str, Any]) -> dict[str, Any]:
    """Attach a canonical hash to terminal and retryable SAT evidence."""

    unsigned = dict(result)
    unsigned.pop("evidence_sha256", None)
    result["evidence_sha256"] = _canonical_sha256(unsigned)
    return result


def _stop_solver_process(
    process: multiprocessing.Process,
    *,
    termination_grace_s: float,
) -> None:
    """Reap exactly one SAT child after cancellation or timeout."""

    if not process.is_alive():
        process.join(timeout=0)
        return
    process.terminate()
    process.join(timeout=termination_grace_s)
    if process.is_alive():
        process.kill()
        process.join(timeout=max(termination_grace_s, 0.1))


def solve_css_threshold_sat(
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    max_weight: int,
    sector: Literal["X", "Z"] | str,
    hard_timeout_s: float,
    cardinality_encoding: str = "seqcounter",
    solver: str = "auto",
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    checkpoint_identity: Mapping[str, Any] | str | None = None,
    partition_index: int | None = None,
    anchor_indices: Sequence[int] | None = None,
    zero_anchor_indices: Sequence[int] | None = None,
    one_anchor_index: int | None = None,
    anchor_cube_sha256: str | None = None,
    cancel_event: Any | None = None,
    termination_grace_s: float = 1.0,
) -> dict[str, Any]:
    """Run one global-sector SAT decision behind a killable wall boundary."""
    native_thread_environment = enforce_sat_native_thread_budget()
    checks, logicals, threshold, sector, encoding = _validated_problem(
        check_matrix,
        target_logicals,
        max_weight=max_weight,
        sector=sector,
        cardinality_encoding=cardinality_encoding,
    )
    hard_timeout = float(hard_timeout_s)
    if not math.isfinite(hard_timeout) or hard_timeout <= 0:
        raise ValueError("hard_timeout_s must be a positive finite number")
    termination_grace = float(termination_grace_s)
    if not math.isfinite(termination_grace) or termination_grace < 0:
        raise ValueError("termination_grace_s must be finite and nonnegative")
    if cancel_event is not None and not callable(
        getattr(cancel_event, "is_set", None),
    ):
        raise ValueError("cancel_event must expose an is_set() method")
    started = time.monotonic()
    partition, anchors, zero_anchors, one_anchor, cube_sha256 = (
        _validated_partition_and_anchors(
            num_logicals=int(logicals.shape[0]),
            n=int(checks.shape[1]),
            partition_index=partition_index,
            anchor_indices=anchor_indices,
            zero_anchor_indices=zero_anchor_indices,
            one_anchor_index=one_anchor_index,
            anchor_cube_sha256=anchor_cube_sha256,
        )
    )
    requested_solver = str(solver).lower()
    if encoding == "native-minicard":
        if requested_solver not in {"auto", "minicard"}:
            raise ValueError(
                "native-minicard encoding may only use solver=minicard or auto"
            )
        requested_solver = "minicard"
    try:
        solver_name = _select_solver(requested_solver)
    except SatBackendUnavailable as exc:
        fallback_binding = {
            "formulation": SAT_FORMULATION,
            "sector": sector,
            "max_weight": threshold,
            "cardinality_encoding": encoding,
            "backend": {
                "distribution": "python-sat",
                "version": _package_version("python-sat"),
                "solver": str(solver),
            },
            "partition_index": partition,
            "anchor_indices": list(anchors),
        }
        if cube_sha256 is not None:
            anchor_unit_clauses = [
                [-(int(index) + 1)] for index in zero_anchors
            ] + [[int(one_anchor) + 1]]
            fallback_binding.update({
                "anchor_constraint_formulation": _ANCHOR_CUBE_FORMULATION,
                "zero_anchor_indices": list(zero_anchors),
                "one_anchor_index": one_anchor,
                "anchor_cube_sha256": cube_sha256,
                "anchor_unit_clauses": anchor_unit_clauses,
                "anchor_unit_clauses_sha256": _canonical_sha256(
                    anchor_unit_clauses,
                ),
            })
        result = _base_evidence(
            binding=fallback_binding,
            hard_timeout_s=hard_timeout,
        )
        result.update({
            "outcome": "backend_unavailable",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": str(exc),
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
            "elapsed_s": time.monotonic() - started,
        })
        return _seal_evidence(result)

    binding = _instance_binding(
        checks,
        logicals,
        max_weight=threshold,
        sector=sector,
        encoding=encoding,
        solver_name=solver_name,
        checkpoint_identity=checkpoint_identity,
        partition_index=partition,
        anchor_indices=anchors,
        zero_anchor_indices=zero_anchors,
        one_anchor_index=one_anchor,
        anchor_cube_sha256=cube_sha256,
    )
    binding["native_thread_environment"] = native_thread_environment
    binding["binding_sha256"] = _canonical_sha256({
        key: value for key, value in binding.items() if key != "binding_sha256"
    })
    checkpoint = Path(checkpoint_path) if checkpoint_path is not None else None
    if checkpoint is not None and resume:
        reused = _load_terminal_checkpoint(
            checkpoint,
            binding=binding,
            checks=checks,
            logicals=logicals,
        )
        if reused is not None:
            return reused

    if cancel_event is not None and cancel_event.is_set():
        result = _base_evidence(binding=binding, hard_timeout_s=hard_timeout)
        result.update({
            "outcome": "cancelled",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": "SAT attempt cancelled before child launch",
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
            "elapsed_s": time.monotonic() - started,
        })
        return _seal_evidence(result)

    context = multiprocessing.get_context("spawn")
    parent, child = context.Pipe(duplex=False)
    process = context.Process(
        target=_solver_worker,
        args=(
            child,
            os.getpid(),
            checks,
            logicals,
            threshold,
            sector,
            encoding,
            solver_name,
            partition,
            anchors,
            zero_anchors,
            one_anchor,
            cube_sha256,
        ),
        daemon=True,
        name=f"qcode-css-{sector.lower()}-threshold-sat",
    )
    process.start()
    child.close()
    message: tuple[Any, ...] | None = None
    interrupted_outcome: str | None = None
    try:
        deadline = started + hard_timeout
        while message is None:
            if cancel_event is not None and cancel_event.is_set():
                interrupted_outcome = "cancelled"
                break
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                interrupted_outcome = "hard_timeout"
                break
            if parent.poll(min(remaining, 0.1)):
                try:
                    message = parent.recv()
                except (EOFError, OSError):
                    message = None
                    if not process.is_alive():
                        break
        if interrupted_outcome is not None:
            _stop_solver_process(
                process,
                termination_grace_s=termination_grace,
            )
    finally:
        parent.close()
        if process.is_alive():
            process.join(timeout=min(termination_grace, 0.2))
        if process.is_alive():
            _stop_solver_process(
                process,
                termination_grace_s=termination_grace,
            )
        process.close()

    result = _base_evidence(binding=binding, hard_timeout_s=hard_timeout)
    if interrupted_outcome is not None:
        result.update({
            "outcome": interrupted_outcome,
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": (
                "SAT attempt cancelled by candidate scheduler"
                if interrupted_outcome == "cancelled"
                else "SAT child exceeded hard wall timeout"
            ),
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
        })
    elif not message:
        result.update({
            "outcome": "worker_exit",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": "SAT child exited without a result",
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
        })
    elif message[0] == "result" and isinstance(message[1], dict):
        result.update(message[1])
        result["retryable"] = False
    elif message[0] == "error":
        result.update({
            "outcome": "solver_error",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": f"{message[1]}: {message[2]}",
            "worker_traceback": message[3],
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
        })
    else:
        result.update({
            "outcome": "worker_exit",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": "SAT child returned a malformed protocol message",
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
        })
    result["elapsed_s"] = time.monotonic() - started

    if result.get("outcome") == "sat":
        failures = verify_css_threshold_sat_witness(result, checks, logicals)
        if failures:
            result.update({
                "outcome": "solver_error",
                "decision_complete": False,
                "threshold_infeasible": False,
                "success": False,
                "retryable": True,
                "message": "SAT witness replay failed: " + "; ".join(failures),
            })
    _seal_evidence(result)
    if checkpoint is not None and result.get("outcome") in SAT_TERMINAL_OUTCOMES:
        _atomic_write_json(checkpoint, result)
    return result


def solve_css_sector_sat(
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    max_weight: int,
    timeout: float,
    workers: int = 1,
    seed: int = 0,
    partition_index: int | None = None,
    anchor_indices: tuple[int, ...] | None = None,
    zero_anchor_indices: tuple[int, ...] | None = None,
    one_anchor_index: int | None = None,
    anchor_cube_sha256: str | None = None,
    sector: Literal["X", "Z"] | str = "Z",
    cardinality_encoding: str = "seqcounter",
    solver: str = "auto",
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    checkpoint_identity: Mapping[str, Any] | str | None = None,
    cancel_event: Any | None = None,
    termination_grace_s: float = 1.0,
) -> dict[str, Any]:
    """Compatibility API for Stage 3/4 global or partitioned decisions.

    python-sat's bundled engines used here are single-threaded.  ``workers``
    and ``seed`` are accepted and recorded so a pipeline can share one solver
    interface with CP-SAT; parallelism should be applied across partitions,
    sectors, encodings, or solvers.
    """
    if isinstance(workers, bool) or not isinstance(workers, int) or workers < 1:
        raise ValueError("workers must be a positive integer")
    if isinstance(seed, bool) or not isinstance(seed, int):
        raise ValueError("seed must be an integer")
    result = solve_css_threshold_sat(
        check_matrix,
        target_logicals,
        max_weight=max_weight,
        sector=sector,
        hard_timeout_s=timeout,
        cardinality_encoding=cardinality_encoding,
        solver=solver,
        checkpoint_path=checkpoint_path,
        resume=resume,
        checkpoint_identity=checkpoint_identity,
        partition_index=partition_index,
        anchor_indices=anchor_indices,
        zero_anchor_indices=zero_anchor_indices,
        one_anchor_index=one_anchor_index,
        anchor_cube_sha256=anchor_cube_sha256,
        cancel_event=cancel_event,
        termination_grace_s=termination_grace_s,
    )
    result["workers"] = int(workers)
    result["random_seed"] = int(seed)
    result["status_name"] = str(result.get("outcome", "unknown")).upper()
    if "evidence_sha256" in result:
        unsigned = dict(result)
        unsigned.pop("evidence_sha256", None)
        result["evidence_sha256"] = _canonical_sha256(unsigned)
    return result


def compose_css_sector_exact_evidence(
    lower_partition_evidence: Sequence[Mapping[str, Any]],
    upper_witness_evidence: Mapping[str, Any],
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    distance: int,
    sector: Literal["X", "Z"] | str,
) -> dict[str, Any]:
    """Compose exact distance ``R`` from ``R-1`` UNSAT plus an ``R`` witness.

    The lower half must contain exactly one complete UNSAT decision for each
    first-nonzero syndrome partition.  Their union is precisely ``Lx != 0``.
    The upper half must be a replayable SAT operator of weight ``R``.  This
    generic matrix-only helper deliberately rejects translation anchors: it
    cannot reconstruct the BB automorphism/orbit proof needed to justify that
    reduction.  Anchored evidence must go through the typed certificate
    verifier, which has the original BB claim and replays that proof.
    """
    checks = np.asarray(check_matrix, dtype=np.uint8) & 1
    logicals = np.asarray(target_logicals, dtype=np.uint8) & 1
    if checks.ndim != 2 or logicals.ndim != 2 or checks.shape[1] != logicals.shape[1]:
        raise ValueError("invalid CSS sector matrices")
    if isinstance(distance, bool) or not isinstance(distance, (int, np.integer)):
        raise ValueError("distance must be an integer")
    exact_distance = int(distance)
    if exact_distance <= 0:
        raise ValueError("distance must be positive")
    normalized_sector = str(sector).upper()
    if normalized_sector not in {"X", "Z"}:
        raise ValueError("sector must be 'X' or 'Z'")
    expected_partitions = set(range(int(logicals.shape[0])))
    observed_partitions: set[int] = set()
    failures: list[str] = []
    used_anchors = False
    check_hash = _array_sha256("checks", checks)
    logical_hash = _array_sha256("logicals", logicals)

    def validate_binding(
        evidence: Mapping[str, Any],
        *,
        label: str,
        expected_partition: int | None,
        expected_weight: int,
    ) -> None:
        nonlocal used_anchors
        unsigned = dict(evidence)
        evidence_hash = unsigned.pop("evidence_sha256", None)
        try:
            evidence_hash_valid = evidence_hash == _canonical_sha256(unsigned)
        except (TypeError, ValueError):
            evidence_hash_valid = False
        if not evidence_hash_valid:
            failures.append(f"{label} has an invalid evidence hash")
        backend = evidence.get("backend")
        if not (
            isinstance(backend, Mapping)
            and backend.get("distribution") == "python-sat"
            and isinstance(backend.get("solver"), str)
            and bool(backend.get("solver"))
        ):
            failures.append(f"{label} has an invalid SAT backend identity")
        instance = evidence.get("instance")
        if not isinstance(instance, Mapping):
            failures.append(f"{label} has no bound instance")
            return
        binding = dict(instance)
        binding_hash = binding.pop("binding_sha256", None)
        try:
            binding_hash_valid = binding_hash == _canonical_sha256(binding)
        except (TypeError, ValueError):
            binding_hash_valid = False
        if not binding_hash_valid:
            failures.append(f"{label} has an invalid instance binding hash")
        anchors = evidence.get("anchor_indices")
        if not isinstance(anchors, list):
            failures.append(f"{label} has invalid anchor indices")
            anchors = []
        if anchors:
            used_anchors = True
        if not (
            evidence.get("schema_version") == SAT_EVIDENCE_SCHEMA_VERSION
            and evidence.get("evidence_kind") == SAT_EVIDENCE_KIND
            and evidence.get("formulation") == SAT_FORMULATION
            and evidence.get("sector") == normalized_sector
            and evidence.get("max_weight") == expected_weight
            and evidence.get("partition_index") == expected_partition
            and instance.get("formulation") == SAT_FORMULATION
            and instance.get("sector") == normalized_sector
            and instance.get("max_weight") == expected_weight
            and instance.get("partition_index") == expected_partition
            and instance.get("anchor_indices") == anchors
            and instance.get("backend") == backend
            and instance.get("check_matrix_sha256") == check_hash
            and instance.get("target_logicals_sha256") == logical_hash
        ):
            failures.append(f"{label} is not bound to the claimed SAT instance")

    for index, raw_evidence in enumerate(lower_partition_evidence):
        evidence = dict(raw_evidence)
        try:
            raw_partition = evidence["partition_index"]
            if isinstance(raw_partition, bool) or not isinstance(
                raw_partition, (int, np.integer),
            ):
                raise ValueError
            partition = int(raw_partition)
        except (KeyError, TypeError, ValueError):
            failures.append(f"lower decision {index} has invalid partition")
            continue
        if partition in observed_partitions:
            failures.append(f"duplicate lower partition {partition}")
        observed_partitions.add(partition)
        if not (
            evidence.get("outcome") == "unsat"
            and evidence.get("decision_complete") is True
            and evidence.get("threshold_infeasible") is True
        ):
            failures.append(f"partition {partition} is not a complete UNSAT decision")
        if evidence.get("max_weight") != exact_distance - 1:
            failures.append(f"partition {partition} used the wrong lower threshold")
        validate_binding(
            evidence,
            label=f"partition {partition}",
            expected_partition=partition,
            expected_weight=exact_distance - 1,
        )
    if observed_partitions != expected_partitions:
        failures.append(
            "lower decisions do not cover every first-nonzero logical partition"
        )
    if used_anchors:
        failures.append(
            "anchored decisions require the code-aware typed certificate verifier"
        )

    upper = dict(upper_witness_evidence)
    validate_binding(
        upper,
        label="upper witness",
        expected_partition=None,
        expected_weight=exact_distance,
    )
    witness_failures = verify_css_threshold_sat_witness(upper, checks, logicals)
    failures.extend(f"upper witness: {failure}" for failure in witness_failures)
    if upper.get("decision_complete") is not True:
        failures.append("upper witness is not a complete SAT decision")
    if upper.get("threshold_infeasible") is not False:
        failures.append("upper witness has invalid feasibility metadata")
    if upper.get("objective") != exact_distance:
        failures.append("upper witness weight does not equal claimed distance")
    if upper.get("max_weight") != exact_distance:
        failures.append("upper witness used the wrong threshold")

    artifact = {
        "schema_version": 1,
        "evidence_kind": "qcode-css-sector-exact-sat-composition",
        "formulation": SAT_FORMULATION,
        "sector": normalized_sector,
        "distance": exact_distance,
        "lower_threshold": exact_distance - 1,
        "num_logicals": int(logicals.shape[0]),
        "expected_partitions": len(expected_partitions),
        "completed_partitions": len(observed_partitions & expected_partitions),
        "matrix_sha256": {
            "checks": check_hash,
            "target_logicals": logical_hash,
        },
        "lower_partition_evidence_sha256": [
            evidence.get("evidence_sha256")
            for evidence in lower_partition_evidence
        ],
        "upper_witness_evidence_sha256": upper.get("evidence_sha256"),
        "anchor_indices": [],
        "failures": failures,
        "exact": not failures,
    }
    artifact["composition_sha256"] = _canonical_sha256(artifact)
    return artifact


def solve_css_code_threshold_sat(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    max_weight: int,
    sector: Literal["X", "Z"] | str,
    **kwargs: Any,
) -> dict[str, Any]:
    """Convenience wrapper selecting the mathematically correct CSS matrices."""
    checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
    return solve_css_threshold_sat(
        checks,
        logicals,
        max_weight=max_weight,
        sector=sector,
        **kwargs,
    )


__all__ = [
    "SAT_AUTO_SOLVERS",
    "SAT_ENCODINGS",
    "SAT_EVIDENCE_KIND",
    "SAT_EVIDENCE_SCHEMA_VERSION",
    "SAT_FORMULATION",
    "SAT_NATIVE_THREAD_ENV",
    "SAT_RETRYABLE_OUTCOMES",
    "SAT_TERMINAL_OUTCOMES",
    "SatBackendUnavailable",
    "build_css_threshold_cnf",
    "compose_css_sector_exact_evidence",
    "css_sector_matrices",
    "enforce_sat_native_thread_budget",
    "pysat_available",
    "solve_css_code_threshold_sat",
    "solve_css_sector_sat",
    "solve_css_threshold_sat",
    "verify_css_threshold_sat_witness",
]
