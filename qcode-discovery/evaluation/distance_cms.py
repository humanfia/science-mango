"""Provisional CSS lower-bound decisions with native CryptoMiniSat XORs.

This module intentionally lives beside, rather than inside, ``distance_sat``.
The two formulations are different: ``distance_sat`` expands parity equations
to Tseitin CNF, while this module emits CryptoMiniSat's native XOR-DIMACS
extension and leaves Gaussian elimination available to the solver.

For a first-nonzero logical partition ``p`` the decision problem is

``H x = 0, L[0:p] x = 0, L[p] x = 1, weight(x) <= max_weight``.

The H and L equations are native XOR constraints.  Only the weight constraint
is encoded to CNF, using PySAT's ``kmtotalizer``.  Translation anchor cubes are
ordinary unit clauses.

Important: CryptoMiniSat's Python API cannot emit proof logs.  The CLI result
returned here is therefore suitable for Stage-3 triage only.  A bare UNSAT
result from this module is *provisional* and must never be promoted to a
publication lower bound.  Publication requires the separate FRAT -> XLRUP ->
``cake_xlrup`` verification path.
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
import tarfile
import tempfile
import time
import urllib.request
from pathlib import Path
from typing import Any, Literal, Mapping, Sequence

import numpy as np


CMS_EVIDENCE_KIND = "qcode-css-threshold-cms-native-xor-evidence"
CMS_EVIDENCE_SCHEMA_VERSION = 1
CMS_FORMULATION = "css-first-nonzero-cms-native-xor-kmtotalizer-v1"
CMS_PROOF_STATUS = "provisional-no-proof-log"

CMS_RELEASE_VERSION = "5.14.7"
CMS_RELEASE_COMMIT = "3c8e228e8a48e41276e8ab039f763daa08d61161"
CMS_RELEASE_LINUX_AMD64_URL = (
    "https://github.com/msoos/cryptominisat/releases/download/"
    "release/v5.14.7/cryptominisat5-v5.14.7-linux-amd64.tar.gz"
)
CMS_RELEASE_LINUX_AMD64_ARCHIVE_SHA256 = (
    "536d4cb03bbd2b4cbcca6230ed30e2aa844f170b5bbcfb0a0d7adb4852cf3ab7"
)

CMS_TERMINAL_OUTCOMES = frozenset({"sat", "unsat"})
CMS_RETRYABLE_OUTCOMES = frozenset({
    "backend_unavailable",
    "hard_timeout",
    "solver_error",
    "unknown",
})

_VERSION_RE = re.compile(r"^c CryptoMiniSat version ([^\s]+)\s*$", re.MULTILINE)
_COMMIT_RE = re.compile(r"^c CMS SHA1: ([0-9a-fA-F]+)\s*$", re.MULTILINE)
_STATUS_RE = re.compile(
    r"^s (SATISFIABLE|UNSATISFIABLE|INDETERMINATE)\s*$",
    re.MULTILINE,
)
_HEX64_RE = re.compile(r"^[0-9a-f]{64}$")

_FIXED_FLAGS = (
    "--verb", "0",
    "--printsol", "1",
    "-t", "1",
    "-r", "0",
    "--maxmatrixrows", "2000",
    "--maxmatrixcols", "1000",
    "--maxnummatrices", "5",
)

try:
    _SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
except OSError:
    _SOURCE_SHA256 = None


class CmsBackendUnavailable(RuntimeError):
    """The pinned CryptoMiniSat executable is missing or has wrong identity."""


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
        raise ValueError("identity must contain strict JSON data") from exc
    return json.loads(encoded)


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _matrix_sha256(name: str, value: np.ndarray) -> str:
    matrix = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode("utf-8"))
    digest.update(b"\0")
    digest.update(json.dumps(list(matrix.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(matrix.tobytes(order="C"))
    return digest.hexdigest()


def _pack_vector(vector: np.ndarray) -> dict[str, Any]:
    binary = np.asarray(vector, dtype=np.uint8).reshape(-1) & 1
    packed = np.packbits(binary, bitorder="little").tobytes()
    return {
        "length": int(binary.size),
        "weight": int(binary.sum()),
        "packed_hex": packed.hex(),
        "sha256": hashlib.sha256(f"{binary.size}:".encode() + packed).hexdigest(),
    }


def unpack_cms_operator(record: Mapping[str, Any]) -> np.ndarray:
    """Decode a packed SAT operator after checking all embedded metadata."""

    try:
        length = int(record["length"])
        packed = bytes.fromhex(str(record["packed_hex"]))
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("invalid packed CMS operator") from exc
    if length < 0:
        raise ValueError("invalid packed CMS operator length")
    vector = np.unpackbits(
        np.frombuffer(packed, dtype=np.uint8), bitorder="little"
    )[:length].astype(np.uint8)
    if _pack_vector(vector) != dict(record):
        raise ValueError("packed CMS operator metadata/hash mismatch")
    return vector


def _validated_problem(
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    partition_index: int,
) -> tuple[np.ndarray, np.ndarray, int, str, int]:
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
    if isinstance(partition_index, bool) or not isinstance(
        partition_index, (int, np.integer)
    ):
        raise ValueError("partition_index must be an integer")
    partition = int(partition_index)
    if not 0 <= partition < int(logicals.shape[0]):
        raise ValueError("partition_index is outside the logical basis")
    return checks, logicals, threshold, normalized_sector, partition


def _validated_anchor_cube(
    n: int,
    *,
    anchor_indices: Sequence[int] | None,
    zero_anchor_indices: Sequence[int] | None,
    one_anchor_index: int | None,
    anchor_cube_sha256: str | None,
) -> tuple[tuple[int, ...], tuple[int, ...], int | None, str | None]:
    def indices(values: Sequence[int] | None, label: str) -> tuple[int, ...]:
        normalized: list[int] = []
        for raw in values or ():
            if isinstance(raw, bool) or not isinstance(raw, (int, np.integer)):
                raise ValueError(f"{label} must contain integers")
            index = int(raw)
            if not 0 <= index < n:
                raise ValueError(f"{label} contains an out-of-range index")
            normalized.append(index)
        if len(set(normalized)) != len(normalized):
            raise ValueError(f"{label} must be distinct")
        return tuple(normalized)

    anchors = indices(anchor_indices, "anchor_indices")
    zeros = indices(zero_anchor_indices, "zero_anchor_indices")
    cube_requested = bool(zeros) or one_anchor_index is not None or (
        anchor_cube_sha256 is not None
    )
    if not cube_requested:
        return anchors, (), None, None
    if not anchors:
        raise ValueError("anchor cube requires nonempty anchor_indices")
    if isinstance(one_anchor_index, bool) or not isinstance(
        one_anchor_index, (int, np.integer)
    ):
        raise ValueError("anchor cube requires an integer one_anchor_index")
    one = int(one_anchor_index)
    if one not in anchors:
        raise ValueError("one_anchor_index must belong to anchor_indices")
    cube_index = anchors.index(one)
    if zeros != anchors[:cube_index]:
        raise ValueError(
            "zero_anchor_indices must be the ordered prefix before one_anchor_index"
        )
    unsigned = {
        "schema_version": 1,
        "cover": "anchor-or-first-nonzero-v1",
        "cube_index": cube_index,
        "zero_anchor_indices": list(zeros),
        "one_anchor_index": one,
        "anchor_indices": list(anchors),
    }
    expected_hash = _canonical_sha256(unsigned)
    if anchor_cube_sha256 != expected_hash:
        raise ValueError("anchor_cube_sha256 does not match the canonical cube")
    return anchors, zeros, one, expected_hash


def cms_anchor_cube_record(
    anchor_indices: Sequence[int], cube_index: int
) -> dict[str, Any]:
    """Return one leaf in the disjoint first-nonzero cover of an anchor OR."""

    anchors = tuple(int(index) for index in anchor_indices)
    if not anchors or len(set(anchors)) != len(anchors) or min(anchors) < 0:
        raise ValueError("anchor_indices must be nonempty, distinct, and nonnegative")
    if isinstance(cube_index, bool) or not isinstance(cube_index, int):
        raise ValueError("cube_index must be an integer")
    if not 0 <= cube_index < len(anchors):
        raise ValueError("cube_index is outside anchor_indices")
    value = {
        "schema_version": 1,
        "cover": "anchor-or-first-nonzero-v1",
        "cube_index": cube_index,
        "zero_anchor_indices": list(anchors[:cube_index]),
        "one_anchor_index": anchors[cube_index],
        "anchor_indices": list(anchors),
    }
    value["cube_sha256"] = _canonical_sha256(value)
    return value


def _xor_dimacs_line(variables: Sequence[int], rhs: bool) -> str | None:
    """Render CMS XOR-DIMACS, whose on-disk right-hand side is always true."""

    items = [int(variable) for variable in variables]
    if not items:
        return None
    # CMS parses ``x lits 0`` as XOR(lits) == True.  Negating one literal
    # flips the parity and therefore represents an even equation.
    if not rhs:
        items[0] = -items[0]
    return "x" + " ".join(str(item) for item in items) + " 0"


def _render_xcnf(
    *,
    num_variables: int,
    clauses: Sequence[Sequence[int]],
    xor_constraints: Sequence[Mapping[str, Any]],
) -> bytes:
    lines = [f"p cnf {int(num_variables)} {len(clauses) + len(xor_constraints)}"]
    for xor in xor_constraints:
        variables = xor["variables"]
        rhs = bool(xor["rhs"])
        line = _xor_dimacs_line(variables, rhs)
        if line is None:
            if rhs:
                lines.append("0")
            continue
        lines.append(line)
    for clause in clauses:
        lines.append(" ".join(str(int(literal)) for literal in clause) + " 0")
    return ("\n".join(lines) + "\n").encode("ascii")


def build_css_threshold_xcnf(
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    max_weight: int,
    sector: Literal["X", "Z"] | str,
    partition_index: int,
    anchor_indices: Sequence[int] | None = None,
    zero_anchor_indices: Sequence[int] | None = None,
    one_anchor_index: int | None = None,
    anchor_cube_sha256: str | None = None,
) -> dict[str, Any]:
    """Build a deterministic native-XOR XCNF threshold instance.

    Variable identifiers ``1..n`` are the operator bits.  Auxiliary variables
    belong exclusively to the kmtotalizer and begin above ``n``.
    """

    checks, logicals, threshold, normalized_sector, partition = _validated_problem(
        check_matrix,
        target_logicals,
        max_weight=max_weight,
        sector=str(sector),
        partition_index=partition_index,
    )
    anchors, zero_anchors, one_anchor, cube_hash = _validated_anchor_cube(
        int(checks.shape[1]),
        anchor_indices=anchor_indices,
        zero_anchor_indices=zero_anchor_indices,
        one_anchor_index=one_anchor_index,
        anchor_cube_sha256=anchor_cube_sha256,
    )
    try:
        from pysat.card import CardEnc, EncType
    except (ImportError, ModuleNotFoundError) as exc:
        raise CmsBackendUnavailable(
            "python-sat is required to build the kmtotalizer"
        ) from exc

    n = int(checks.shape[1])
    operator_variables = list(range(1, n + 1))
    encoded = CardEnc.atmost(
        lits=operator_variables,
        bound=threshold,
        top_id=n,
        encoding=EncType.kmtotalizer,
    )
    clauses = [[int(literal) for literal in clause] for clause in encoded.clauses]
    if cube_hash is not None:
        clauses.extend([[-(index + 1)] for index in zero_anchors])
        clauses.append([int(one_anchor) + 1])
    elif anchors:
        # Legacy unsplit form, retained for controlled A/B comparisons.  New
        # lower-bound scheduling should pass an explicit cube instead.
        clauses.append([index + 1 for index in anchors])

    xor_constraints: list[dict[str, Any]] = []
    for row in checks:
        variables = [int(index) + 1 for index in np.flatnonzero(row)]
        if variables:
            xor_constraints.append({"variables": variables, "rhs": False})
    for logical_index in range(partition):
        variables = [
            int(index) + 1 for index in np.flatnonzero(logicals[logical_index])
        ]
        if variables:
            xor_constraints.append({"variables": variables, "rhs": False})
    pivot_variables = [
        int(index) + 1 for index in np.flatnonzero(logicals[partition])
    ]
    if pivot_variables:
        xor_constraints.append({"variables": pivot_variables, "rhs": True})
    else:
        # Empty XOR == 1 is false.  A normal empty clause is understood by CMS
        # and keeps the XCNF renderer/parser simple.
        clauses.append([])

    num_variables = max(n, int(encoded.nv))
    xcnf = _render_xcnf(
        num_variables=num_variables,
        clauses=clauses,
        xor_constraints=xor_constraints,
    )
    return {
        "formulation": CMS_FORMULATION,
        "sector": normalized_sector,
        "n": n,
        "num_checks": int(checks.shape[0]),
        "num_logicals": int(logicals.shape[0]),
        "partition_index": partition,
        "max_weight": threshold,
        "cardinality_encoding": "kmtotalizer",
        "operator_variables": operator_variables,
        "num_variables": num_variables,
        "num_normal_clauses": len(clauses),
        "num_xor_constraints": len(xor_constraints),
        "clauses": clauses,
        "xor_constraints": xor_constraints,
        "anchor_indices": list(anchors),
        "zero_anchor_indices": list(zero_anchors),
        "one_anchor_index": one_anchor,
        "anchor_cube_sha256": cube_hash,
        "xcnf": xcnf.decode("ascii"),
        "xcnf_sha256": hashlib.sha256(xcnf).hexdigest(),
    }


def _run_version_command(path: Path, timeout_s: float = 5.0) -> str:
    process = subprocess.Popen(
        [str(path), "--version"],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout_s)
    except subprocess.TimeoutExpired:
        _terminate_process_group(process, grace_s=0.2)
        raise CmsBackendUnavailable("CryptoMiniSat --version timed out")
    if process.returncode != 0:
        raise CmsBackendUnavailable(
            f"CryptoMiniSat --version exited with status {process.returncode}"
        )
    try:
        output = (stdout + stderr).decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise CmsBackendUnavailable("CryptoMiniSat --version is not UTF-8") from exc
    if len(output.encode("utf-8")) > 1024 * 1024:
        raise CmsBackendUnavailable("CryptoMiniSat --version output is excessive")
    return output


def inspect_cryptominisat_binary(
    binary: Path | str,
    *,
    require_official_release: bool = True,
) -> dict[str, Any]:
    """Hash and identify an executable before it is admitted to a proof run."""

    requested = Path(binary).expanduser()
    try:
        resolved = requested.resolve(strict=True)
        metadata = resolved.stat()
    except OSError as exc:
        raise CmsBackendUnavailable(f"CryptoMiniSat binary is unavailable: {exc}") from exc
    if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved, os.X_OK):
        raise CmsBackendUnavailable("CryptoMiniSat path is not an executable file")
    output = _run_version_command(resolved)
    version_match = _VERSION_RE.search(output)
    commit_match = _COMMIT_RE.search(output)
    if version_match is None or commit_match is None:
        raise CmsBackendUnavailable("CryptoMiniSat version identity is incomplete")
    version = version_match.group(1)
    commit = commit_match.group(1).lower()
    if require_official_release and (
        version != CMS_RELEASE_VERSION or commit != CMS_RELEASE_COMMIT
    ):
        raise CmsBackendUnavailable(
            "CryptoMiniSat is not the pinned official v5.14.7 release"
        )
    identity = {
        "backend": "cryptominisat-cli-native-xor",
        "requested_path": str(requested.absolute()),
        "resolved_path": str(resolved),
        "file_size": int(metadata.st_size),
        "file_mode": stat.S_IMODE(metadata.st_mode),
        "file_sha256": _file_sha256(resolved),
        "reported_version": version,
        "reported_commit": commit,
        "version_output_sha256": hashlib.sha256(output.encode("utf-8")).hexdigest(),
        "official_release_required": bool(require_official_release),
    }
    identity["identity_sha256"] = _canonical_sha256(identity)
    return identity


def _process_group_exists(process_group: int) -> bool:
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _terminate_process_group(
    process: subprocess.Popen[bytes], *, grace_s: float
) -> dict[str, Any]:
    """Terminate and reap a private session, escalating to SIGKILL."""

    process_group = int(process.pid)
    sent_term = False
    sent_kill = False
    try:
        os.killpg(process_group, signal.SIGTERM)
        sent_term = True
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=grace_s)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process_group, signal.SIGKILL)
            sent_kill = True
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=max(1.0, grace_s))
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError("CryptoMiniSat process could not be reaped") from exc

    # The leader may have exited while a descendant kept the group alive.
    if _process_group_exists(process_group):
        try:
            os.killpg(process_group, signal.SIGKILL)
            sent_kill = True
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + max(1.0, grace_s)
        while _process_group_exists(process_group) and time.monotonic() < deadline:
            time.sleep(0.01)
    return {
        "process_group": process_group,
        "sent_sigterm": sent_term,
        "sent_sigkill": sent_kill,
        "leader_reaped": process.poll() is not None,
        "group_survived": _process_group_exists(process_group),
    }


def _parse_solver_output(
    stdout: bytes,
    *,
    returncode: int,
    n: int,
) -> tuple[str, np.ndarray | None, str | None]:
    try:
        text = stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError:
        return "solver_error", None, "solver stdout is not UTF-8"
    statuses = _STATUS_RE.findall(text)
    if len(statuses) != 1:
        return "solver_error", None, "solver emitted missing or ambiguous status"
    status = statuses[0]
    expected_code = {
        "SATISFIABLE": 10,
        "UNSATISFIABLE": 20,
        "INDETERMINATE": 15,
    }[status]
    if returncode != expected_code:
        return "solver_error", None, "solver status and exit code disagree"
    if status == "UNSATISFIABLE":
        return "unsat", None, None
    if status == "INDETERMINATE":
        return "unknown", None, "solver returned INDETERMINATE"

    literals: list[int] = []
    terminated = False
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped.startswith("v"):
            continue
        for token in stripped[1:].split():
            try:
                literal = int(token)
            except ValueError:
                return "solver_error", None, "SAT model contains a non-integer"
            if literal == 0:
                terminated = True
                continue
            if terminated:
                return "solver_error", None, "SAT model has literals after terminator"
            literals.append(literal)
    if not terminated:
        return "solver_error", None, "SAT result has no terminated model"
    assignments: dict[int, bool] = {}
    for literal in literals:
        variable = abs(literal)
        value = literal > 0
        if variable in assignments and assignments[variable] != value:
            return "solver_error", None, "SAT model assigns a variable twice"
        assignments[variable] = value
    missing = [variable for variable in range(1, n + 1) if variable not in assignments]
    if missing:
        return "solver_error", None, "SAT model omits operator variables"
    vector = np.fromiter(
        (int(assignments[index]) for index in range(1, n + 1)),
        dtype=np.uint8,
        count=n,
    )
    return "sat", vector, None


def _operator_failures(
    vector: np.ndarray,
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    partition_index: int,
    anchors: Sequence[int],
    zero_anchors: Sequence[int],
    one_anchor: int | None,
) -> list[str]:
    failures: list[str] = []
    if vector.size != checks.shape[1]:
        return ["operator width mismatch"]
    if np.any((checks @ vector) & 1):
        failures.append("operator has nonzero stabilizer syndrome")
    syndrome = ((logicals @ vector) & 1).astype(int).tolist()
    if any(syndrome[:partition_index]) or syndrome[partition_index] != 1:
        failures.append("operator violates first-nonzero logical partition")
    if int(vector.sum()) > max_weight:
        failures.append("operator exceeds threshold")
    if one_anchor is None:
        if anchors and not any(int(vector[index]) for index in anchors):
            failures.append("operator violates anchor OR")
    else:
        if any(int(vector[index]) for index in zero_anchors):
            failures.append("operator violates zero anchor units")
        if int(vector[one_anchor]) != 1:
            failures.append("operator violates one anchor unit")
    return failures


def verify_cms_sat_witness(
    evidence: Mapping[str, Any],
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
) -> list[str]:
    """Replay a CMS SAT witness algebraically without trusting the solver."""

    if evidence.get("outcome") != "sat":
        return ["evidence does not contain a SAT witness"]
    try:
        vector = unpack_cms_operator(evidence["operator"])
        threshold = int(evidence["max_weight"])
        partition = int(evidence["partition_index"])
        anchors = [int(index) for index in evidence.get("anchor_indices", [])]
        zeros = [int(index) for index in evidence.get("zero_anchor_indices", [])]
        raw_one = evidence.get("one_anchor_index")
        one = None if raw_one is None else int(raw_one)
    except (KeyError, TypeError, ValueError) as exc:
        return [f"invalid SAT witness metadata: {exc}"]
    checks = np.asarray(check_matrix, dtype=np.uint8) & 1
    logicals = np.asarray(target_logicals, dtype=np.uint8) & 1
    failures = _operator_failures(
        vector,
        checks,
        logicals,
        max_weight=threshold,
        partition_index=partition,
        anchors=anchors,
        zero_anchors=zeros,
        one_anchor=one,
    )
    syndrome = ((logicals @ vector) & 1).astype(int).tolist()
    if evidence.get("logical_syndrome") != syndrome:
        failures.append("stored logical syndrome does not match operator")
    if evidence.get("objective") != int(vector.sum()):
        failures.append("objective does not equal operator weight")
    return failures


def _sealed(value: Mapping[str, Any]) -> dict[str, Any]:
    result = _canonical_json(value)
    result["evidence_sha256"] = _canonical_sha256(result)
    return result


def solve_css_threshold_cms(
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    *,
    max_weight: int,
    sector: Literal["X", "Z"] | str,
    partition_index: int,
    hard_timeout_s: float,
    binary: Path | str,
    anchor_indices: Sequence[int] | None = None,
    zero_anchor_indices: Sequence[int] | None = None,
    one_anchor_index: int | None = None,
    anchor_cube_sha256: str | None = None,
    force_gaussian: bool = True,
    termination_grace_s: float = 1.0,
    require_official_release: bool = True,
    checkpoint_identity: Mapping[str, Any] | str | None = None,
) -> dict[str, Any]:
    """Run one native-XOR threshold decision behind a hard process boundary.

    The function never downloads or installs a solver.  ``binary`` must name an
    already provisioned executable.  UNSAT is explicitly marked provisional.
    """

    checks, logicals, threshold, normalized_sector, partition = _validated_problem(
        check_matrix,
        target_logicals,
        max_weight=max_weight,
        sector=str(sector),
        partition_index=partition_index,
    )
    hard_timeout = float(hard_timeout_s)
    grace = float(termination_grace_s)
    if not math.isfinite(hard_timeout) or hard_timeout <= 0:
        raise ValueError("hard_timeout_s must be a positive finite number")
    if not math.isfinite(grace) or grace < 0:
        raise ValueError("termination_grace_s must be finite and nonnegative")
    started = time.monotonic()
    try:
        xcnf = build_css_threshold_xcnf(
            checks,
            logicals,
            max_weight=threshold,
            sector=normalized_sector,
            partition_index=partition,
            anchor_indices=anchor_indices,
            zero_anchor_indices=zero_anchor_indices,
            one_anchor_index=one_anchor_index,
            anchor_cube_sha256=anchor_cube_sha256,
        )
        binary_identity = inspect_cryptominisat_binary(
            binary, require_official_release=require_official_release
        )
    except CmsBackendUnavailable as exc:
        return _sealed({
            "schema_version": CMS_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": CMS_EVIDENCE_KIND,
            "outcome": "backend_unavailable",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "publication_lower_bound_eligible": False,
            "proof_status": CMS_PROOF_STATUS,
            "message": str(exc),
            "sector": normalized_sector,
            "partition_index": partition,
            "max_weight": threshold,
            "operator": None,
            "objective": None,
            "elapsed_s": time.monotonic() - started,
        })

    soft_timeout = max(0.001, hard_timeout * 0.95)
    flags = list(_FIXED_FLAGS)
    if force_gaussian:
        flags.extend(["--autodisablegauss", "0"])
    flags.extend(["--maxtime", format(soft_timeout, ".9g")])
    binding: dict[str, Any] = {
        "formulation": CMS_FORMULATION,
        "source_sha256": _SOURCE_SHA256,
        "sector": normalized_sector,
        "n": int(checks.shape[1]),
        "num_checks": int(checks.shape[0]),
        "num_logicals": int(logicals.shape[0]),
        "partition_index": partition,
        "max_weight": threshold,
        "cardinality_encoding": "kmtotalizer",
        "check_matrix_sha256": _matrix_sha256("checks", checks),
        "target_logicals_sha256": _matrix_sha256("logicals", logicals),
        "xcnf_sha256": xcnf["xcnf_sha256"],
        "xcnf_num_variables": xcnf["num_variables"],
        "xcnf_num_normal_clauses": xcnf["num_normal_clauses"],
        "xcnf_num_xor_constraints": xcnf["num_xor_constraints"],
        "anchor_indices": xcnf["anchor_indices"],
        "zero_anchor_indices": xcnf["zero_anchor_indices"],
        "one_anchor_index": xcnf["one_anchor_index"],
        "anchor_cube_sha256": xcnf["anchor_cube_sha256"],
        "backend": binary_identity,
        "solver_flags": flags,
        "hard_timeout_s": hard_timeout,
        "checkpoint_identity": (
            None
            if checkpoint_identity is None
            else _canonical_json(checkpoint_identity)
        ),
        "proof_status": CMS_PROOF_STATUS,
    }
    binding["binding_sha256"] = _canonical_sha256(binding)
    base: dict[str, Any] = {
        "schema_version": CMS_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": CMS_EVIDENCE_KIND,
        "formulation": CMS_FORMULATION,
        "instance": binding,
        "backend": binary_identity,
        "sector": normalized_sector,
        "partition_index": partition,
        "max_weight": threshold,
        "cardinality_encoding": "kmtotalizer",
        "anchor_indices": xcnf["anchor_indices"],
        "zero_anchor_indices": xcnf["zero_anchor_indices"],
        "one_anchor_index": xcnf["one_anchor_index"],
        "anchor_cube_sha256": xcnf["anchor_cube_sha256"],
        "publication_lower_bound_eligible": False,
        "proof_status": CMS_PROOF_STATUS,
        "hard_timeout_s": hard_timeout,
    }

    xcnf_bytes = xcnf["xcnf"].encode("ascii")
    process: subprocess.Popen[bytes] | None = None
    stdout = b""
    stderr = b""
    cleanup: dict[str, Any] | None = None
    with tempfile.TemporaryDirectory(prefix="qcode-cms-") as temporary:
        input_path = Path(temporary) / "instance.xcnf"
        with input_path.open("wb") as stream:
            stream.write(xcnf_bytes)
            stream.flush()
            os.fsync(stream.fileno())
        command = [binary_identity["resolved_path"], *flags, str(input_path)]
        try:
            process = subprocess.Popen(
                command,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            if os.getpgid(process.pid) != process.pid:
                raise RuntimeError("CryptoMiniSat did not establish a private session")
            try:
                stdout, stderr = process.communicate(timeout=hard_timeout)
            except subprocess.TimeoutExpired:
                cleanup = _terminate_process_group(process, grace_s=grace)
                stdout, stderr = process.communicate()
                result = dict(base)
                result.update({
                    "outcome": "hard_timeout",
                    "decision_complete": False,
                    "threshold_infeasible": False,
                    "retryable": True,
                    "message": "CryptoMiniSat exceeded hard wall timeout",
                    "operator": None,
                    "objective": None,
                    "logical_syndrome": None,
                    "returncode": process.returncode,
                    "cleanup": cleanup,
                    "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                    "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
                    "elapsed_s": time.monotonic() - started,
                })
                return _sealed(result)
        except (OSError, RuntimeError) as exc:
            if process is not None and process.poll() is None:
                cleanup = _terminate_process_group(process, grace_s=grace)
                stdout, stderr = process.communicate()
            result = dict(base)
            result.update({
                "outcome": "solver_error",
                "decision_complete": False,
                "threshold_infeasible": False,
                "retryable": True,
                "message": f"CryptoMiniSat could not run safely: {exc}",
                "operator": None,
                "objective": None,
                "logical_syndrome": None,
                "cleanup": cleanup,
                "elapsed_s": time.monotonic() - started,
            })
            return _sealed(result)

    assert process is not None and process.returncode is not None
    group_survived = _process_group_exists(process.pid)
    if group_survived:
        cleanup = _terminate_process_group(process, grace_s=grace)
    try:
        post_identity = inspect_cryptominisat_binary(
            binary,
            require_official_release=require_official_release,
        )
    except CmsBackendUnavailable as exc:
        post_identity = None
        identity_error = str(exc)
    else:
        identity_error = None
    outcome, vector, parse_error = _parse_solver_output(
        stdout,
        returncode=int(process.returncode),
        n=int(checks.shape[1]),
    )
    if post_identity != binary_identity:
        outcome = "solver_error"
        vector = None
        parse_error = identity_error or "CryptoMiniSat binary identity changed during run"
    if group_survived:
        outcome = "solver_error"
        vector = None
        parse_error = "CryptoMiniSat left descendant processes"
    if len(stdout) > 16 * 1024 * 1024 or len(stderr) > 16 * 1024 * 1024:
        outcome = "solver_error"
        vector = None
        parse_error = "CryptoMiniSat output exceeded the safety limit"

    result = dict(base)
    result.update({
        "outcome": outcome,
        "decision_complete": outcome in CMS_TERMINAL_OUTCOMES,
        "threshold_infeasible": outcome == "unsat",
        "retryable": outcome in CMS_RETRYABLE_OUTCOMES,
        "message": parse_error,
        "operator": None,
        "objective": None,
        "logical_syndrome": None,
        "returncode": int(process.returncode),
        "cleanup": cleanup,
        "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
        "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
        "elapsed_s": time.monotonic() - started,
    })
    if outcome == "sat" and vector is not None:
        failures = _operator_failures(
            vector,
            checks,
            logicals,
            max_weight=threshold,
            partition_index=partition,
            anchors=xcnf["anchor_indices"],
            zero_anchors=xcnf["zero_anchor_indices"],
            one_anchor=xcnf["one_anchor_index"],
        )
        if failures:
            result.update({
                "outcome": "solver_error",
                "decision_complete": False,
                "threshold_infeasible": False,
                "retryable": True,
                "message": "SAT model failed algebraic replay: " + "; ".join(failures),
            })
        else:
            result["operator"] = _pack_vector(vector)
            result["objective"] = int(vector.sum())
            result["logical_syndrome"] = (
                (logicals @ vector) & 1
            ).astype(int).tolist()
    return _sealed(result)


def bootstrap_official_cryptominisat(
    destination_directory: Path | str,
) -> dict[str, Any]:
    """Explicitly download and install the pinned official Linux-amd64 CLI.

    Calling this function performs network I/O.  Solver calls never invoke it.
    The release archive is accepted only after matching the hard-coded SHA-256,
    and only the regular ``cryptominisat5`` member is extracted.
    """

    destination = Path(destination_directory).expanduser().resolve()
    destination.mkdir(parents=True, exist_ok=True)
    target = destination / f"cryptominisat5-v{CMS_RELEASE_VERSION}"
    if target.exists():
        return inspect_cryptominisat_binary(target, require_official_release=True)

    archive_path: Path | None = None
    temporary_target: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            prefix="cms-release-", suffix=".tar.gz", dir=destination, delete=False
        ) as archive_stream:
            archive_path = Path(archive_stream.name)
            with urllib.request.urlopen(
                CMS_RELEASE_LINUX_AMD64_URL, timeout=60
            ) as response:
                total = 0
                while True:
                    block = response.read(1024 * 1024)
                    if not block:
                        break
                    total += len(block)
                    if total > 32 * 1024 * 1024:
                        raise CmsBackendUnavailable("CMS release archive is unexpectedly large")
                    archive_stream.write(block)
            archive_stream.flush()
            os.fsync(archive_stream.fileno())
        if _file_sha256(archive_path) != CMS_RELEASE_LINUX_AMD64_ARCHIVE_SHA256:
            raise CmsBackendUnavailable("CMS release archive SHA-256 mismatch")
        with tarfile.open(archive_path, mode="r:gz") as archive:
            members = [
                member
                for member in archive.getmembers()
                if member.isfile() and Path(member.name).name == "cryptominisat5"
            ]
            if len(members) != 1:
                raise CmsBackendUnavailable(
                    "CMS release archive does not contain one regular cryptominisat5"
                )
            source = archive.extractfile(members[0])
            if source is None:
                raise CmsBackendUnavailable("cannot read CMS release executable")
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=".cryptominisat5-", dir=destination
            )
            temporary_target = Path(temporary_name)
            try:
                with os.fdopen(descriptor, "wb") as output:
                    while True:
                        block = source.read(1024 * 1024)
                        if not block:
                            break
                        output.write(block)
                    output.flush()
                    os.fsync(output.fileno())
            finally:
                source.close()
        temporary_target.chmod(0o755)
        identity = inspect_cryptominisat_binary(
            temporary_target, require_official_release=True
        )
        os.replace(temporary_target, target)
        temporary_target = None
        installed = inspect_cryptominisat_binary(target, require_official_release=True)
        if identity["file_sha256"] != installed["file_sha256"]:
            raise CmsBackendUnavailable("CMS executable changed during atomic install")
        return installed
    finally:
        if archive_path is not None:
            try:
                archive_path.unlink()
            except FileNotFoundError:
                pass
        if temporary_target is not None:
            try:
                temporary_target.unlink()
            except FileNotFoundError:
                pass


__all__ = [
    "CMS_EVIDENCE_KIND",
    "CMS_FORMULATION",
    "CMS_PROOF_STATUS",
    "CMS_RELEASE_COMMIT",
    "CMS_RELEASE_LINUX_AMD64_ARCHIVE_SHA256",
    "CMS_RELEASE_LINUX_AMD64_URL",
    "CMS_RELEASE_VERSION",
    "CmsBackendUnavailable",
    "bootstrap_official_cryptominisat",
    "build_css_threshold_xcnf",
    "cms_anchor_cube_record",
    "inspect_cryptominisat_binary",
    "solve_css_threshold_cms",
    "unpack_cms_operator",
    "verify_cms_sat_witness",
]
