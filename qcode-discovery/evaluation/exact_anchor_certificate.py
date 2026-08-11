"""Proof-carrying exact-distance certificate for one installed calibration anchor.

This versioned verifier adds the missing publication layer above
``evaluation.distance_sat``: a bare UNSAT
status is not accepted. Both sector CNFs are rebuilt byte-for-byte and pinned
DRAT-trim plus independent LRAT-check binaries both replay carried proofs.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import math
import os
import stat
import subprocess
import tempfile
from contextlib import contextmanager
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Mapping, Sequence

import numpy as np

from evaluation.css_logical_detector import (
    CSS_LOGICAL_DETECTOR_METHOD,
    verify_css_logical_detectors,
)
from evaluation.coset_two_block import matrix_sha256
from evaluation.distance_sat import (
    SAT_FORMULATION,
    _FORMULATION_REVISION,
    _array_sha256,
    build_css_threshold_cnf,
    css_sector_matrices,
)
from evaluation.matrix_certificate import _rebuild_claim
from evaluation.matrix_io import parse_binary_matrix
from evaluation.target_policy import TARGET_MODE_SCALAR, target_binding
from evolve.coset_search_contract import (
    coset_candidate_digest,
    normalize_coset_candidate,
)


SCHEMA_VERSION = 1
CERTIFICATE_TYPE = "qcode-css-exact-anchor-proof-carrying-v1"
MATRIX_BUNDLE_KIND = "qcode-css-proof-matrix-bundle-v1"
CERTIFICATE_ROLE = "published-calibration"
HASH_CHUNK_BYTES = 1 << 20
MAX_MATRIX_BUNDLE_BYTES = 1 << 28
MAX_ISOMETRY_ARTIFACT_BYTES = 1 << 24
MAX_CHECKER_POLICY_BYTES = 1 << 20
MAX_DIMACS_BYTES = 1 << 36
MAX_CHECKER_BINARY_BYTES = 1 << 30
MAX_CHECKER_SOURCE_BYTES = 1 << 30
MAX_TRUSTED_PROOF_BYTES = 1 << 50
MAX_CHECKER_OUTPUT_BYTES = 1 << 20
MAX_CHECKER_TIMEOUT_S = 7 * 24 * 60 * 60
GLOBAL_COVER = "global-logical-or-v1"
PARTITION_COVER = "first-nonzero-logical-partition-cover-v1"
SYMMETRY_COVER = "symmetry-anchor-cover-v1"
XZ_ISOMETRY_KIND = "qcode-css-xz-sector-isometry-v1"
XZ_ISOMETRY_HASH_METHOD = "uint32-little-endian-raw-sha256-v1"
CHECKER_POLICY_KIND = "qcode-proof-checker-trust-policy-v1"
DRAT_CHECKER_ROLE = "drat-trim-verify"
LRAT_CHECKER_ROLE = "lrat-check"
_CHECKER_SUCCESS_LINES = {
    "drat": b"s VERIFIED",
    "lrat": b"c VERIFIED",
}
_HEX = frozenset("0123456789abcdef")

_INSTALLED_ACTION_ID = "coset2bga-l224-m53-s1-degree112-v2"
_INSTALLED_CANDIDATE = {
    "schema_version": 3,
    "representation_id": "css-coset-two-block-actions-v3",
    "renderer_descriptor_id": "catalog-combination-walk-v3",
    "action_id": _INSTALLED_ACTION_ID,
    "support_split": [3, 3],
    "left_support": ["L000", "L104", "L207"],
    "right_support": ["R000", "R009", "R024"],
}
_INSTALLED_CANDIDATE_SHA256 = (
    "2ebf783fe6d991e0bf03b318f4aaeb01c246f59d6558e4ba4b7d79bdf6c61969"
)


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _strict_json_equal(left: Any, right: Any) -> bool:
    """Compare JSON values without Python's bool/int/float coercions."""

    try:
        return _canonical_json_bytes(left) == _canonical_json_bytes(right)
    except (TypeError, ValueError):
        return False


def _reject_duplicate_json_keys(pairs: Sequence[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number is forbidden: {value}")


def _load_strict_json(stream) -> Any:
    return json.load(
        stream,
        object_pairs_hook=_reject_duplicate_json_keys,
        parse_constant=_reject_json_constant,
    )


def _loads_strict_json(payload: bytes | str) -> Any:
    return json.loads(
        payload,
        object_pairs_hook=_reject_duplicate_json_keys,
        parse_constant=_reject_json_constant,
    )


def canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    if omit is not None and isinstance(value, Mapping):
        value = {key: item for key, item in value.items() if key != omit}
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def checker_semantic_stdout_sha256(proof_format: str) -> str:
    try:
        success_line = _CHECKER_SUCCESS_LINES[proof_format]
    except KeyError as exc:
        raise ValueError("proof format has no checker success semantics") from exc
    return hashlib.sha256(success_line + b"\n").hexdigest()


def seal_certificate(certificate: Mapping[str, Any]) -> dict[str, Any]:
    sealed = json.loads(json.dumps(certificate))
    sealed.pop("certificate_sha256", None)
    sealed["certificate_sha256"] = canonical_sha256(sealed)
    return sealed


def permutation_sha256(permutation: Sequence[int]) -> str:
    """Hash an explicitly ordered permutation with a fixed portable encoding."""

    if not isinstance(permutation, Sequence) or isinstance(
        permutation, (str, bytes, bytearray)
    ):
        raise ValueError("permutation must be an integer sequence")
    if any(
        type(value) is not int or value < 0 or value > 0xFFFFFFFF
        for value in permutation
    ):
        raise ValueError("permutation contains a non-uint32 value")
    return hashlib.sha256(
        np.asarray(permutation, dtype="<u4").tobytes(order="C")
    ).hexdigest()


def build_xz_isometry_artifact(
    *,
    hx: np.ndarray,
    hz: np.ndarray,
    row_permutation: Sequence[int],
    qubit_permutation: Sequence[int],
    proof_sector: str = "X",
) -> dict[str, Any]:
    """Build the canonical self-hashed X/Z isometry payload."""

    matrix_x = np.asarray(hx, dtype=np.uint8) & 1
    matrix_z = np.asarray(hz, dtype=np.uint8) & 1
    if matrix_x.ndim != 2 or matrix_z.shape != matrix_x.shape:
        raise ValueError("X/Z isometry requires equal-shaped binary check matrices")
    if proof_sector not in {"X", "Z"}:
        raise ValueError("proof_sector must be X or Z")
    rows = list(row_permutation)
    qubits = list(qubit_permutation)
    artifact: dict[str, Any] = {
        "schema_version": 1,
        "kind": XZ_ISOMETRY_KIND,
        "hash_method": XZ_ISOMETRY_HASH_METHOD,
        "proof_sector": proof_sector,
        "derived_sector": "Z" if proof_sector == "X" else "X",
        "dimensions": {
            "check_rows": int(matrix_x.shape[0]),
            "qubits": int(matrix_x.shape[1]),
        },
        "matrix_sha256": {
            "H_X": matrix_sha256(matrix_x),
            "H_Z": matrix_sha256(matrix_z),
        },
        "row_permutation": rows,
        "row_permutation_sha256": permutation_sha256(rows),
        "qubit_permutation": qubits,
        "qubit_permutation_sha256": permutation_sha256(qubits),
        "forward_identity": "H_X[row_permutation,qubit_permutation]==H_Z",
        "reverse_identity": "H_Z[row_permutation,qubit_permutation]==H_X",
    }
    artifact["artifact_sha256"] = canonical_sha256(artifact)
    return artifact


def _iter_dimacs_bytes(cnf: Mapping[str, Any]):
    if cnf.get("native_atmost") is not None:
        raise ValueError("publication DIMACS cannot carry native at-most clauses")
    variables = int(cnf["num_variables"])
    clauses = cnf["clauses"]
    yield f"p cnf {variables} {len(clauses)}\n".encode("ascii")
    for clause in clauses:
        yield (
            " ".join(str(int(literal)) for literal in clause) + " 0\n"
        ).encode("ascii")


def render_dimacs(cnf: Mapping[str, Any]) -> bytes:
    """Canonical serialization paired with ``build_css_threshold_cnf``."""

    return b"".join(_iter_dimacs_bytes(cnf))


def _dimacs_matches(stream, cnf: Mapping[str, Any]) -> bool:
    """Compare canonical DIMACS without reading either full stream twice."""

    stream.seek(0)
    try:
        for expected in _iter_dimacs_bytes(cnf):
            if stream.read(len(expected)) != expected:
                return False
        return stream.read(1) == b""
    finally:
        stream.seek(0)


def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in _HEX for character in value)
    )


def _source_fingerprint(metadata: os.stat_result) -> tuple[int, ...]:
    """Metadata that must remain stable while a source FD is snapshotted."""

    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _new_snapshot_fd(label: str) -> int:
    """Create an anonymous inode that can be sealed against every later write."""

    required = (
        "memfd_create",
        "MFD_ALLOW_SEALING",
    )
    if any(not hasattr(os, name) for name in required) or any(
        not hasattr(fcntl, name)
        for name in (
            "F_ADD_SEALS",
            "F_SEAL_SEAL",
            "F_SEAL_SHRINK",
            "F_SEAL_GROW",
            "F_SEAL_WRITE",
        )
    ):
        raise OSError("immutable verifier snapshots are unavailable")
    flags = os.MFD_ALLOW_SEALING | getattr(os, "MFD_CLOEXEC", 0)
    return os.memfd_create(f"qcode-verifier-{label}", flags)


@contextmanager
def _immutable_snapshot_from_fd(
    source_fd: int,
    *,
    label: str,
    expected_bytes: int,
    expected_sha256: str | None,
    executable: bool = False,
):
    """Copy, authenticate, seal, and expose a verifier-owned private inode."""

    initial = os.fstat(source_fd)
    if not stat.S_ISREG(initial.st_mode):
        raise ValueError(f"{label} source FD is not a regular file")
    if initial.st_size != expected_bytes:
        raise ValueError(f"{label} source FD byte count mismatch")
    if executable and initial.st_mode & 0o111 == 0:
        raise ValueError(f"{label} source FD is not executable")

    snapshot_fd = _new_snapshot_fd(label.replace("/", "-")[-128:])
    snapshot_stream = None
    try:
        digest = hashlib.sha256()
        copied = 0
        os.lseek(source_fd, 0, os.SEEK_SET)
        while copied <= expected_bytes:
            remaining = expected_bytes + 1 - copied
            chunk = os.read(source_fd, min(HASH_CHUNK_BYTES, remaining))
            if not chunk:
                break
            copied += len(chunk)
            if copied > expected_bytes:
                raise ValueError(f"{label} source FD byte count mismatch")
            digest.update(chunk)
            view = memoryview(chunk)
            while view:
                written = os.write(snapshot_fd, view)
                if written <= 0:  # pragma: no cover - os.write either writes or raises
                    raise OSError("short write while creating verifier snapshot")
                view = view[written:]
        final = os.fstat(source_fd)
        if _source_fingerprint(final) != _source_fingerprint(initial):
            raise ValueError(f"{label} source changed while being snapshotted")
        if copied != expected_bytes:
            raise ValueError(f"{label} source FD byte count mismatch")
        if expected_sha256 is not None and digest.hexdigest() != expected_sha256:
            raise ValueError(f"{label} source FD SHA-256 mismatch")
        if os.fstat(snapshot_fd).st_size != expected_bytes:
            raise OSError("verifier snapshot byte count mismatch")

        os.fchmod(snapshot_fd, 0o500 if executable else 0o400)
        seals = (
            fcntl.F_SEAL_SEAL
            | fcntl.F_SEAL_SHRINK
            | fcntl.F_SEAL_GROW
            | fcntl.F_SEAL_WRITE
        )
        fcntl.fcntl(snapshot_fd, fcntl.F_ADD_SEALS, seals)
        os.lseek(snapshot_fd, 0, os.SEEK_SET)
        snapshot_stream = os.fdopen(snapshot_fd, "rb", closefd=True)
        snapshot_fd = -1
        yield snapshot_stream
    finally:
        if snapshot_stream is not None:
            snapshot_stream.close()
        if snapshot_fd >= 0:
            os.close(snapshot_fd)


def _read_capped_stream(stream, *, max_bytes: int) -> bytes | None:
    stream.flush()
    size = stream.seek(0, os.SEEK_END)
    stream.seek(0)
    if size > max_bytes:
        return None
    return stream.read()


def _validate_checker_timeout_s(value: Any) -> float:
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or value <= 0
        or value > MAX_CHECKER_TIMEOUT_S
        or not math.isfinite(float(value))
    ):
        raise ValueError(
            "checker_timeout_s must be a positive finite number no greater "
            f"than {MAX_CHECKER_TIMEOUT_S}"
        )
    return float(value)


def _validate_max_proof_bytes(value: Any) -> int:
    if (
        isinstance(value, bool)
        or not isinstance(value, int)
        or value <= 0
        or value > MAX_TRUSTED_PROOF_BYTES
    ):
        raise ValueError(
            "max_proof_bytes must be a positive integer no greater than "
            f"{MAX_TRUSTED_PROOF_BYTES}"
        )
    return value


def load_trusted_checker_policy(
    path: Path | str,
) -> dict[str, dict[str, Any]]:
    """Load a sealed two-checker policy with no certificate-supplied trust."""

    policy_path = Path(path)
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    policy_fd = -1
    try:
        policy_fd = os.open(policy_path, flags)
        metadata = os.fstat(policy_fd)
        if not stat.S_ISREG(metadata.st_mode):
            raise ValueError("trusted checker policy must be a regular file")
        if not 0 < metadata.st_size <= MAX_CHECKER_POLICY_BYTES:
            raise ValueError("trusted checker policy size is invalid")
        with _immutable_snapshot_from_fd(
            policy_fd,
            label="trusted checker policy",
            expected_bytes=metadata.st_size,
            expected_sha256=None,
        ) as stream:
            payload = stream.read(MAX_CHECKER_POLICY_BYTES + 1)
            if len(payload) != metadata.st_size:
                raise ValueError("trusted checker policy size is invalid")
            raw = _loads_strict_json(payload)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("trusted checker policy is not strict JSON") from exc
    finally:
        if policy_fd >= 0:
            os.close(policy_fd)
    top = _exact_keys(
        raw,
        {"schema_version", "kind", "checkers", "policy_sha256"},
        where="trusted checker policy",
    )
    if (
        type(top["schema_version"]) is not int
        or top["schema_version"] != 1
        or top["kind"] != CHECKER_POLICY_KIND
        or top["policy_sha256"]
        != canonical_sha256(top, omit="policy_sha256")
    ):
        raise ValueError("trusted checker policy identity/self hash mismatch")
    return _normalize_trusted_checkers(top["checkers"])


def _normalize_trusted_checkers(
    checkers: Any,
) -> dict[str, dict[str, Any]]:
    if not isinstance(checkers, Mapping) or len(checkers) != 2:
        raise ValueError("trusted checker policy must contain exactly two checkers")
    expected_roles = {
        DRAT_CHECKER_ROLE: "drat",
        LRAT_CHECKER_ROLE: "lrat",
    }
    normalized: dict[str, dict[str, Any]] = {}
    observed_roles: set[str] = set()
    binary_hashes: set[str] = set()
    timeouts: set[float] = set()
    for checker_id, raw_checker in checkers.items():
        if not isinstance(checker_id, str) or not checker_id:
            raise ValueError("trusted checker ID must be a nonempty string")
        checker = _exact_keys(
            raw_checker,
            {
                "checker_role",
                "proof_format",
                "binary_sha256",
                "source_repository",
                "source_commit",
                "source_sha256",
                "argv_roles",
                "semantic_stdout_sha256",
                "timeout_s",
                "max_proof_bytes",
            },
            where=f"trusted checker policy.{checker_id}",
        )
        role = checker["checker_role"]
        if role not in expected_roles or checker["proof_format"] != expected_roles[role]:
            raise ValueError("trusted checker role/proof format mismatch")
        if role in observed_roles:
            raise ValueError("trusted checker roles must be unique")
        observed_roles.add(role)
        if not _is_sha256(checker["binary_sha256"]):
            raise ValueError("trusted checker binary SHA-256 is invalid")
        if checker["binary_sha256"] in binary_hashes:
            raise ValueError("trusted checker binaries must be distinct")
        binary_hashes.add(checker["binary_sha256"])
        if not _is_sha256(checker["source_sha256"]):
            raise ValueError("trusted checker source SHA-256 is invalid")
        if not isinstance(checker["source_repository"], str) or not checker[
            "source_repository"
        ]:
            raise ValueError("trusted checker source repository is invalid")
        commit = checker["source_commit"]
        if not (
            isinstance(commit, str)
            and len(commit) in {40, 64}
            and all(character in _HEX for character in commit)
        ):
            raise ValueError("trusted checker source commit is invalid")
        if checker["argv_roles"] != ["binary", "dimacs", "proof"]:
            raise ValueError("trusted checker argv roles are invalid")
        if checker["semantic_stdout_sha256"] != checker_semantic_stdout_sha256(
            checker["proof_format"]
        ):
            raise ValueError("trusted checker semantic stdout binding is invalid")
        timeouts.add(_validate_checker_timeout_s(checker["timeout_s"]))
        _validate_max_proof_bytes(checker["max_proof_bytes"])
        normalized[checker_id] = dict(checker)
    if observed_roles != set(expected_roles):
        raise ValueError("trusted checker policy lacks the two required roles")
    if len(timeouts) != 1:
        raise ValueError("trusted checker policies must use one exact timeout")
    return normalized


def _exact_keys(
    value: Any,
    required: set[str],
    *,
    where: str,
) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{where} must be an object")
    if set(value) != required:
        raise ValueError(
            f"{where} fields are not exact: missing={sorted(required - set(value))}, "
            f"unknown={sorted(set(value) - required)}"
        )
    return value


def build_exact_anchor_certificate(certificate: Mapping[str, Any]) -> dict[str, Any]:
    """Seal one already assembled proof-carrying calibration certificate.

    This packaging step never invokes a SAT/MILP solver or trusts the supplied
    payload.  The independent verifier below still rebuilds every matrix/CNF
    binding and replays every proof checker.  Requiring the explicit type here
    prevents ordinary matrix claims from entering the anchor-only path.
    """

    payload = json.loads(json.dumps(certificate))
    payload.pop("certificate_sha256", None)
    _exact_keys(
        payload,
        {
            "schema_version",
            "certificate_type",
            "certificate_role",
            "anchor",
            "construction",
            "parameters",
            "matrix_bundle",
            "distance_proof",
            "target",
            "disposition",
        },
        where="exact anchor certificate payload",
    )
    if payload["certificate_type"] != CERTIFICATE_TYPE:
        raise ValueError("explicit exact anchor certificate_type is required")
    if payload["certificate_role"] != CERTIFICATE_ROLE:
        raise ValueError("exact anchor certificate_role must be published-calibration")
    if type(payload["schema_version"]) is not int or payload["schema_version"] != 1:
        raise ValueError("exact anchor certificate schema_version must be integer 1")
    return seal_certificate(payload)


def _resolve_artifact_path(
    root: Path,
    descriptor: Mapping[str, Any],
    *,
    label: str,
    max_bytes: int,
) -> Path:
    _exact_keys(descriptor, {"path", "bytes", "sha256"}, where=label)
    raw_path = descriptor["path"]
    if not isinstance(raw_path, str) or not raw_path:
        raise ValueError(f"{label}.path must be a nonempty relative POSIX path")
    pure = PurePosixPath(raw_path)
    if pure.is_absolute() or any(part in {"", ".", ".."} for part in pure.parts):
        raise ValueError(f"{label}.path is unsafe")
    if (
        type(descriptor["bytes"]) is not int
        or not 0 <= descriptor["bytes"] <= max_bytes
    ):
        raise ValueError(f"{label}.bytes is invalid")
    if not _is_sha256(descriptor["sha256"]):
        raise ValueError(f"{label}.sha256 is invalid")
    if root.is_symlink():
        raise ValueError("artifact root must not be a symlink")
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError("artifact root must be a real directory")
    cursor = root
    for part in pure.parts:
        cursor = cursor / part
        metadata = cursor.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            raise ValueError(f"{label} traverses a symlink")
    resolved = cursor.resolve(strict=True)
    if resolved.parent != root and root not in resolved.parents:
        raise ValueError(f"{label} escapes the artifact root")
    metadata = resolved.stat()
    if not stat.S_ISREG(metadata.st_mode):
        raise ValueError(f"{label} is not a regular file")
    if metadata.st_size != descriptor["bytes"]:
        raise ValueError(f"{label} byte count mismatch")
    return resolved


@contextmanager
def _open_pinned_artifact(
    root: Path,
    descriptor: Mapping[str, Any],
    *,
    label: str,
    max_bytes: int,
    require_executable: bool = False,
):
    """Consume only a sealed private snapshot of an authenticated artifact."""

    resolved = _resolve_artifact_path(
        root,
        descriptor,
        label=label,
        max_bytes=max_bytes,
    )
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    descriptor_fd = os.open(resolved, flags)
    try:
        metadata = os.fstat(descriptor_fd)
        if not stat.S_ISREG(metadata.st_mode):
            raise ValueError(f"{label} source FD is not a regular file")
        if require_executable and metadata.st_mode & 0o111 == 0:
            raise ValueError(f"{label} source FD is not executable")
        if metadata.st_size != descriptor["bytes"]:
            raise ValueError(f"{label} source FD byte count mismatch")
        with _immutable_snapshot_from_fd(
            descriptor_fd,
            label=label,
            expected_bytes=descriptor["bytes"],
            expected_sha256=descriptor["sha256"],
            executable=require_executable,
        ) as snapshot:
            yield snapshot
    finally:
        if descriptor_fd >= 0:
            os.close(descriptor_fd)


def _load_matrix_bundle(stream) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    try:
        stream.seek(0)
        raw = _load_strict_json(stream)
        stream.seek(0)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("matrix bundle is not strict JSON") from exc
    bundle = _exact_keys(
        raw,
        {
            "schema_version",
            "kind",
            "logical_basis_method",
            "H_X",
            "H_Z",
            "L_X",
            "L_Z",
            "bundle_sha256",
        },
        where="matrix bundle",
    )
    if (
        type(bundle["schema_version"]) is not int
        or bundle["schema_version"] != 1
        or bundle["kind"] != MATRIX_BUNDLE_KIND
        or bundle["logical_basis_method"] != CSS_LOGICAL_DETECTOR_METHOD
        or bundle["bundle_sha256"] != canonical_sha256(bundle, omit="bundle_sha256")
    ):
        raise ValueError("matrix bundle identity mismatch")
    matrices = {
        key: parse_binary_matrix(bundle[key], name=key)
        for key in ("H_X", "H_Z", "L_X", "L_Z")
    }
    return matrices, dict(bundle)


def _strict_permutation(
    value: Any,
    *,
    size: int,
    label: str,
) -> np.ndarray:
    if not isinstance(value, list) or len(value) != size:
        raise ValueError(f"{label} must contain exactly {size} entries")
    if any(type(item) is not int for item in value):
        raise ValueError(f"{label} entries must be exact integers")
    if sorted(value) != list(range(size)):
        raise ValueError(f"{label} is not a bijection over 0..{size - 1}")
    permutation = np.asarray(value, dtype=np.int64)
    if not np.array_equal(permutation[permutation], np.arange(size)):
        raise ValueError(f"{label} is not an involution")
    return permutation


def _validate_xz_isometry_artifact(
    descriptor: Mapping[str, Any],
    *,
    root: Path,
    hx: np.ndarray,
    hz: np.ndarray,
    supplied_proof_sector: str,
) -> dict[str, Any]:
    """Replay a carried isometry against authoritative rebuilt matrices."""

    try:
        with _open_pinned_artifact(
            root,
            descriptor,
            label="lower_bound.xz_isometry",
            max_bytes=MAX_ISOMETRY_ARTIFACT_BYTES,
        ) as stream:
            raw = _load_strict_json(stream)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("X/Z isometry artifact is not strict JSON") from exc
    artifact = _exact_keys(
        raw,
        {
            "schema_version",
            "kind",
            "hash_method",
            "proof_sector",
            "derived_sector",
            "dimensions",
            "matrix_sha256",
            "row_permutation",
            "row_permutation_sha256",
            "qubit_permutation",
            "qubit_permutation_sha256",
            "forward_identity",
            "reverse_identity",
            "artifact_sha256",
        },
        where="X/Z isometry artifact",
    )
    if (
        type(artifact["schema_version"]) is not int
        or artifact["schema_version"] != 1
        or artifact["kind"] != XZ_ISOMETRY_KIND
        or artifact["hash_method"] != XZ_ISOMETRY_HASH_METHOD
        or artifact["artifact_sha256"]
        != canonical_sha256(artifact, omit="artifact_sha256")
    ):
        raise ValueError("X/Z isometry artifact identity/self hash mismatch")
    matrix_x = np.asarray(hx, dtype=np.uint8) & 1
    matrix_z = np.asarray(hz, dtype=np.uint8) & 1
    if matrix_x.ndim != 2 or matrix_z.shape != matrix_x.shape:
        raise ValueError("authoritative X/Z matrices do not have one common shape")
    rows, qubits = matrix_x.shape
    dimensions = _exact_keys(
        artifact["dimensions"], {"check_rows", "qubits"}, where="isometry dimensions"
    )
    if not _strict_json_equal(dimensions, {"check_rows": rows, "qubits": qubits}):
        raise ValueError("X/Z isometry dimensions mismatch")
    matrix_hashes = _exact_keys(
        artifact["matrix_sha256"], {"H_X", "H_Z"}, where="isometry matrix hashes"
    )
    expected_matrix_hashes = {
        "H_X": matrix_sha256(matrix_x),
        "H_Z": matrix_sha256(matrix_z),
    }
    if not _strict_json_equal(matrix_hashes, expected_matrix_hashes):
        raise ValueError("X/Z isometry matrix hash binding mismatch")
    row_permutation = _strict_permutation(
        artifact["row_permutation"], size=rows, label="row_permutation"
    )
    qubit_permutation = _strict_permutation(
        artifact["qubit_permutation"], size=qubits, label="qubit_permutation"
    )
    if artifact["row_permutation_sha256"] != permutation_sha256(
        artifact["row_permutation"]
    ):
        raise ValueError("row permutation hash mismatch")
    if artifact["qubit_permutation_sha256"] != permutation_sha256(
        artifact["qubit_permutation"]
    ):
        raise ValueError("qubit permutation hash mismatch")
    if (
        artifact["proof_sector"] not in {"X", "Z"}
        or artifact["derived_sector"]
        != ("Z" if artifact["proof_sector"] == "X" else "X")
        or supplied_proof_sector != artifact["proof_sector"]
    ):
        raise ValueError("X/Z isometry proof/derived sector direction mismatch")
    if artifact["forward_identity"] != "H_X[row_permutation,qubit_permutation]==H_Z":
        raise ValueError("X/Z isometry forward identity descriptor mismatch")
    if artifact["reverse_identity"] != "H_Z[row_permutation,qubit_permutation]==H_X":
        raise ValueError("X/Z isometry reverse identity descriptor mismatch")
    if not np.array_equal(
        matrix_x[np.ix_(row_permutation, qubit_permutation)], matrix_z
    ):
        raise ValueError("X/Z isometry forward matrix identity failed")
    if not np.array_equal(
        matrix_z[np.ix_(row_permutation, qubit_permutation)], matrix_x
    ):
        raise ValueError("X/Z isometry reverse matrix identity failed")
    return dict(artifact)


def installed_anchor_policy() -> dict[str, Any]:
    """Resolve the exact installed catalog record; metadata is never caller data."""

    from evaluation.coset_action_catalog import V2_CATALOG_ID, list_action_descriptors

    descriptor = next(
        item
        for item in list_action_descriptors(catalog_id=V2_CATALOG_ID)
        if item["action_id"] == _INSTALLED_ACTION_ID
    )
    candidate = normalize_coset_candidate(_INSTALLED_CANDIDATE)
    if coset_candidate_digest(candidate) != _INSTALLED_CANDIDATE_SHA256:
        raise RuntimeError("installed calibration candidate identity changed")
    published = descriptor["published_support"]
    if not (
        type(published["reported_n"]) is int
        and published["reported_n"] == 224
        and type(published["reported_k"]) is int
        and published["reported_k"] == 12
        and type(published["reported_distance"]) is int
        and published["reported_distance"] == 16
        and published["reported_distance_exact"] is True
    ):
        raise RuntimeError("installed published anchor parameters changed")
    source = descriptor["source_bindings"]
    if len(source) != 1:
        raise RuntimeError("installed published anchor source is ambiguous")
    provenance = descriptor["provenance"]
    anchor = {
        "candidate_sha256": _INSTALLED_CANDIDATE_SHA256,
        "candidate": candidate,
        "action_catalog": {
            "catalog_id": descriptor["action_catalog_id"],
            "schema_version": descriptor["action_catalog_schema_version"],
            "sha256": descriptor["action_catalog_sha256"],
        },
        "paper": {
            "identifier": provenance["paper"],
            "upstream_repository": provenance["upstream_repository"],
            "upstream_commit": provenance["upstream_commit"],
            "source_record": dict(source[0]),
        },
        "published_support": dict(published),
    }
    construction = {
        "kind": "coset-two-block-v2",
        "representation_id": "css-coset-two-block-actions-v2",
        "action_id": candidate["action_id"],
        "action_catalog_id": descriptor["action_catalog_id"],
        "action_catalog_sha256": descriptor["action_catalog_sha256"],
        "left_support": list(candidate["left_support"]),
        "right_support": list(candidate["right_support"]),
    }
    return {
        "anchor": anchor,
        "construction": construction,
        "n": 224,
        "k": 12,
        "distance": 16,
        "target": target_binding(224, 12, TARGET_MODE_SCALAR),
    }


def _default_authoritative_matrices(
    construction: Mapping[str, Any],
) -> tuple[np.ndarray, np.ndarray]:
    _code, hx, hz, _normalized, _identity, _source = _rebuild_claim(
        {"construction": dict(construction)}
    )
    return np.asarray(hx, dtype=np.uint8) & 1, np.asarray(hz, dtype=np.uint8) & 1


def _validate_witness(
    witness: Mapping[str, Any],
    *,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    distance: int,
) -> list[str]:
    failures: list[str] = []
    try:
        _exact_keys(
            witness,
            {"sector", "weight", "bits", "support", "logical_syndrome", "witness_sha256"},
            where="upper witness",
        )
        if witness["witness_sha256"] != canonical_sha256(witness, omit="witness_sha256"):
            failures.append("upper witness self hash mismatch")
        sector = witness["sector"]
        if sector not in {"X", "Z"}:
            raise ValueError("upper witness sector must be X or Z")
        bits = witness["bits"]
        if not isinstance(bits, list) or len(bits) != hx.shape[1] or any(type(bit) is not int or bit not in {0, 1} for bit in bits):
            raise ValueError("upper witness bits are not an n-bit binary vector")
        vector = np.asarray(bits, dtype=np.uint8)
        support = [int(index) for index in np.flatnonzero(vector)]
        if not _strict_json_equal(witness["support"], support):
            failures.append("upper witness support does not match bits")
        if (
            type(witness["weight"]) is not int
            or witness["weight"] != int(vector.sum())
            or witness["weight"] != distance
        ):
            failures.append("upper witness is not exact claimed weight")
        checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
        syndrome = ((logicals @ vector) & 1).astype(int).tolist()
        if np.any((checks @ vector) & 1):
            failures.append("upper witness has nonzero stabilizer syndrome")
        if not any(syndrome):
            failures.append("upper witness is trivial in the logical quotient")
        if not _strict_json_equal(witness["logical_syndrome"], syndrome):
            failures.append("upper witness logical syndrome mismatch")
    except (KeyError, TypeError, ValueError) as exc:
        failures.append(f"upper witness malformed: {exc}")
    return failures


def _validate_checker(
    proof_check: Mapping[str, Any],
    *,
    root: Path,
    trusted_checkers: Mapping[str, Mapping[str, Any]],
    dimacs_stream,
    label: str,
    expected_format: str,
    expected_role: str,
    checker_timeout_s: float,
) -> list[str]:
    failures: list[str] = []
    try:
        proof_check = _exact_keys(
            proof_check,
            {"proof", "checker"},
            where=label,
        )
        proof = _exact_keys(
            proof_check["proof"],
            {"format", "artifact"},
            where=f"{label}.proof",
        )
        proof_format = proof["format"]
        if proof_format != expected_format:
            raise ValueError(f"proof format must be exactly {expected_format}")
        checker = _exact_keys(
            proof_check["checker"],
            {
                "checker_role",
                "checker_id",
                "proof_format",
                "binary",
                "source",
                "run",
            },
            where=f"{label}.checker",
        )
        if checker["checker_role"] != expected_role:
            raise ValueError(f"checker role must be exactly {expected_role}")
        checker_id = checker["checker_id"]
        if not isinstance(checker_id, str) or not checker_id:
            raise ValueError("checker_id must be a nonempty string")
        policy = trusted_checkers.get(checker_id)
        if not isinstance(policy, Mapping):
            raise ValueError("checker is not in the trusted verifier policy")
        policy_timeout_s = _validate_checker_timeout_s(policy.get("timeout_s"))
        if policy_timeout_s != checker_timeout_s:
            raise ValueError("checker timeout differs from trusted verifier policy")
        max_proof_bytes = _validate_max_proof_bytes(policy.get("max_proof_bytes"))
        source = _exact_keys(
            checker["source"],
            {"repository", "commit", "artifact"},
            where=f"{label}.checker.source",
        )
        if not isinstance(source["repository"], str) or not source["repository"]:
            raise ValueError("checker source repository is invalid")
        if not (
            isinstance(source["commit"], str)
            and len(source["commit"]) in {40, 64}
            and all(character in _HEX for character in source["commit"])
        ):
            raise ValueError("checker source commit is invalid")
        run = _exact_keys(
            checker["run"],
            {
                "argv_roles",
                "exit_code",
                "stdout_sha256",
                "stderr_sha256",
                "semantic_stdout_sha256",
            },
            where=f"{label}.checker.run",
        )
        with _open_pinned_artifact(
            root,
            source["artifact"],
            label=f"{label}.checker.source.artifact",
            max_bytes=MAX_CHECKER_SOURCE_BYTES,
        ):
            pass
        expected = {
            "checker_role": expected_role,
            "proof_format": proof_format,
            "binary_sha256": checker["binary"]["sha256"],
            "source_repository": source["repository"],
            "source_commit": source["commit"],
            "source_sha256": source["artifact"]["sha256"],
            "argv_roles": run["argv_roles"],
            "semantic_stdout_sha256": run["semantic_stdout_sha256"],
            "timeout_s": policy["timeout_s"],
            "max_proof_bytes": max_proof_bytes,
        }
        if not _strict_json_equal(dict(policy), expected):
            raise ValueError("checker identity does not match trusted verifier policy")
        if checker["proof_format"] != proof_format:
            raise ValueError("checker/proof format mismatch")
        if run["argv_roles"] != ["binary", "dimacs", "proof"]:
            raise ValueError("checker argv roles are not the fixed safe invocation")
        if type(run["exit_code"]) is not int or run["exit_code"] != 0:
            raise ValueError("recorded checker exit is not zero")
        if not _is_sha256(run["stdout_sha256"]) or not _is_sha256(run["stderr_sha256"]):
            raise ValueError("recorded checker stream hash is invalid")
        if run["semantic_stdout_sha256"] != checker_semantic_stdout_sha256(
            proof_format
        ):
            raise ValueError("checker semantic stdout binding is invalid")
        with _open_pinned_artifact(
            root,
            checker["binary"],
            label=f"{label}.checker.binary",
            max_bytes=MAX_CHECKER_BINARY_BYTES,
            require_executable=True,
        ) as binary_stream, _open_pinned_artifact(
            root,
            proof["artifact"],
            label=f"{label}.proof.artifact",
            max_bytes=max_proof_bytes,
        ) as proof_stream:
            dimacs_stream.seek(0)
            binary_stream.seek(0)
            proof_stream.seek(0)
            inherited_fds = (
                binary_stream.fileno(),
                dimacs_stream.fileno(),
                proof_stream.fileno(),
            )
            inherited_paths = [
                f"/proc/self/fd/{descriptor_fd}" for descriptor_fd in inherited_fds
            ]
            with tempfile.TemporaryFile() as stdout_stream, tempfile.TemporaryFile() as stderr_stream:
                completed = subprocess.run(
                    inherited_paths,
                    cwd=root,
                    stdin=subprocess.DEVNULL,
                    stdout=stdout_stream,
                    stderr=stderr_stream,
                    timeout=checker_timeout_s,
                    check=False,
                    pass_fds=inherited_fds,
                    env={
                        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                        "LC_ALL": "C",
                    },
                )
                stdout = _read_capped_stream(
                    stdout_stream,
                    max_bytes=MAX_CHECKER_OUTPUT_BYTES,
                )
                stderr = _read_capped_stream(
                    stderr_stream,
                    max_bytes=MAX_CHECKER_OUTPUT_BYTES,
                )
        if stdout is None or stderr is None:
            failures.append(f"{label} checker output exceeded cap")
        if completed.returncode != 0 or completed.returncode != run["exit_code"]:
            failures.append(f"{label} checker exit mismatch")
        # Raw stream hashes are immutable generation provenance. Official
        # checkers print nondeterministic timing, so fresh acceptance binds the
        # stable semantic line instead of requiring byte-identical stdout.
        semantic_lines = (
            []
            if stdout is None
            else [
                line
                for line in stdout.splitlines()
                if line == _CHECKER_SUCCESS_LINES[proof_format]
            ]
        )
        if len(semantic_lines) != 1:
            failures.append(f"{label} checker semantic success marker missing")
        if stderr != b"":
            failures.append(f"{label} checker fresh stderr is not empty")
    except (KeyError, OSError, subprocess.SubprocessError, TypeError, ValueError) as exc:
        failures.append(f"{label} checker validation failed: {exc}")
    return failures


def _validate_dual_proof_checks(
    proof_checks: Any,
    *,
    root: Path,
    trusted_checkers: Mapping[str, Mapping[str, Any]],
    dimacs_stream,
    label: str,
    checker_timeout_s: float,
) -> list[str]:
    """Require independent DRAT and LRAT replays over the same DIMACS file."""

    failures: list[str] = []
    required = {
        "drat": DRAT_CHECKER_ROLE,
        "lrat": LRAT_CHECKER_ROLE,
    }
    try:
        checks = _exact_keys(proof_checks, set(required), where=f"{label}.proof_checks")
        identities: list[tuple[str, str]] = []
        for proof_format, checker_role in required.items():
            check = checks[proof_format]
            failures.extend(
                _validate_checker(
                    check,
                    root=root,
                    trusted_checkers=trusted_checkers,
                    dimacs_stream=dimacs_stream,
                    label=f"{label}.proof_checks.{proof_format}",
                    expected_format=proof_format,
                    expected_role=checker_role,
                    checker_timeout_s=checker_timeout_s,
                )
            )
            checker = check.get("checker") if isinstance(check, Mapping) else None
            if isinstance(checker, Mapping):
                identities.append(
                    (
                        str(checker.get("checker_id")),
                        str(
                            checker.get("binary", {}).get("sha256")
                            if isinstance(checker.get("binary"), Mapping)
                            else None
                        ),
                    )
                )
        if len(identities) != 2 or len(set(identities)) != 2:
            failures.append(f"{label} DRAT/LRAT checker identities are not independent")
        if len({item[0] for item in identities}) != 2:
            failures.append(f"{label} DRAT/LRAT checker IDs must be distinct")
        if len({item[1] for item in identities}) != 2:
            failures.append(f"{label} DRAT/LRAT checker binaries must be distinct")
    except (KeyError, TypeError, ValueError) as exc:
        failures.append(f"{label} dual proof validation failed: {exc}")
    return failures


def _expected_partition_indices(
    *,
    cover: str,
    k: int,
    units: Sequence[Mapping[str, Any]],
) -> list[int | None]:
    """Fail closed on the only two exhaustive logical-sector covers."""

    observed = [unit.get("partition_index") for unit in units]
    if cover == GLOBAL_COVER:
        if observed != [None]:
            raise ValueError("global logical OR cover requires one null partition")
        return [None]
    if cover == PARTITION_COVER:
        if any(type(index) is not int for index in observed):
            raise ValueError(
                "first-nonzero partition indices must be exact integers ordered "
                "exactly 0..k-1"
            )
        expected = list(range(k))
        if not _strict_json_equal(observed, expected):
            raise ValueError(
                "first-nonzero partition indices must be ordered exactly 0..k-1"
            )
        return expected
    raise ValueError("unknown lower-bound logical cover")


def _construction_symmetry_report(
    construction: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
) -> dict[str, Any]:
    from scripts.screen_frontier_sat import verify_construction_symmetry

    return verify_construction_symmetry(
        {"construction": dict(construction)}, hx, hz,
    )


def _symmetry_unit_cover(
    units: Sequence[Mapping[str, Any]],
    cubes: Sequence[Mapping[str, Any]],
) -> list[None]:
    if len(units) != len(cubes):
        raise ValueError("sector must contain every symmetry anchor cube")
    if [unit.get("partition_index") for unit in units] != [None] * len(cubes):
        raise ValueError("symmetry anchor units must use global logical OR")
    if not _strict_json_equal(
        [unit.get("anchor_cube") for unit in units],
        list(cubes),
    ):
        raise ValueError("symmetry anchor cubes are not the complete ordered cover")
    return [None] * len(cubes)


def _validate_certificate(
    certificate: Mapping[str, Any],
    *,
    artifact_root: Path | str,
    trusted_checkers: Mapping[str, Mapping[str, Any]],
    checker_timeout_s: float,
    policy: Mapping[str, Any],
    authoritative_matrix_builder: Callable[[Mapping[str, Any]], tuple[np.ndarray, np.ndarray]],
) -> dict[str, Any]:
    checker_timeout_s = _validate_checker_timeout_s(checker_timeout_s)
    failures: list[str] = []
    root = Path(artifact_root)
    try:
        trusted_checkers = _normalize_trusted_checkers(trusted_checkers)
        if any(type(policy.get(key)) is not int for key in ("n", "k", "distance")):
            raise ValueError("verifier policy n/k/d must be exact integers")
        policy_target = policy.get("target")
        if not isinstance(policy_target, Mapping) or type(
            policy_target.get("required_distance")
        ) is not int:
            raise ValueError(
                "verifier policy target.required_distance must be an exact integer"
            )
        top = _exact_keys(
            certificate,
            {
                "schema_version",
                "certificate_type",
                "certificate_role",
                "anchor",
                "construction",
                "parameters",
                "matrix_bundle",
                "distance_proof",
                "target",
                "disposition",
                "certificate_sha256",
            },
            where="certificate",
        )
        if (
            type(top["schema_version"]) is not int
            or top["schema_version"] != SCHEMA_VERSION
            or top["certificate_type"] != CERTIFICATE_TYPE
        ):
            failures.append("certificate schema/type mismatch")
        if top["certificate_role"] != CERTIFICATE_ROLE:
            failures.append("certificate is not a published calibration")
        if top["certificate_sha256"] != canonical_sha256(top, omit="certificate_sha256"):
            failures.append("certificate self hash mismatch")
        if not _strict_json_equal(top["anchor"], policy["anchor"]):
            failures.append("anchor/catalog/paper/source binding mismatch")
        if not _strict_json_equal(top["construction"], policy["construction"]):
            failures.append("construction binding mismatch")
        parameters = _exact_keys(top["parameters"], {"n", "k", "d"}, where="parameters")
        expected_parameters = {
            "n": policy["n"],
            "k": policy["k"],
            "d": policy["distance"],
        }
        if any(type(parameters[key]) is not int for key in ("n", "k", "d")) or not (
            _strict_json_equal(parameters, expected_parameters)
        ):
            failures.append("published parameters mismatch")
        if not _strict_json_equal(top["target"], policy["target"]):
            failures.append("target binding mismatch")
        target_unsigned = dict(top["target"])
        target_hash = target_unsigned.pop("binding_sha256", None)
        if target_hash != canonical_sha256(target_unsigned):
            failures.append("target self hash mismatch")
        expected_disposition = {
            "classification": "published-calibration",
            "novelty": "known-published-non-novel",
            "calibration_only": True,
            "target_threshold_satisfied": policy["distance"] >= policy["target"]["required_distance"],
            "selected_win_eligible": False,
            "trusted_win_eligible": False,
            "formal_win_eligible": False,
            "win_awarded": False,
        }
        if not _strict_json_equal(top["disposition"], expected_disposition):
            failures.append("calibration/non-novel no-win disposition mismatch")

        with _open_pinned_artifact(
            root,
            top["matrix_bundle"],
            label="matrix_bundle",
            max_bytes=MAX_MATRIX_BUNDLE_BYTES,
        ) as bundle_stream:
            matrices, _bundle = _load_matrix_bundle(bundle_stream)
        hx, hz, lx, lz = (matrices[key] for key in ("H_X", "H_Z", "L_X", "L_Z"))
        authoritative_hx, authoritative_hz = authoritative_matrix_builder(top["construction"])
        authoritative_hx = np.asarray(authoritative_hx, dtype=np.uint8) & 1
        authoritative_hz = np.asarray(authoritative_hz, dtype=np.uint8) & 1
        if not np.array_equal(hx, authoritative_hx) or not np.array_equal(hz, authoritative_hz):
            failures.append("H_X/H_Z do not match authoritative construction rebuild")
        detector = verify_css_logical_detectors(hx, hz, lx, lz)
        if detector.get("verified") is not True:
            failures.append("logical basis completeness/duality replay failed")
        if detector.get("n") != policy["n"] or detector.get("k") != policy["k"]:
            failures.append("matrix/logical parameters mismatch")

        proof = _exact_keys(
            top["distance_proof"],
            {"claimed_distance", "lower_bound", "upper_bound"},
            where="distance_proof",
        )
        if (
            type(proof["claimed_distance"]) is not int
            or proof["claimed_distance"] != policy["distance"]
        ):
            failures.append("exact-distance claim mismatch")
        raw_lower = proof["lower_bound"]
        if not isinstance(raw_lower, Mapping):
            raise ValueError("lower_bound must be an object")
        legacy_lower_keys = {"max_weight", "symmetry", "sectors"}
        isometric_lower_keys = legacy_lower_keys | {"xz_isometry"}
        if set(raw_lower) == legacy_lower_keys:
            lower = raw_lower
            isometry_descriptor = None
        elif set(raw_lower) == isometric_lower_keys:
            lower = raw_lower
            isometry_descriptor = lower["xz_isometry"]
            if not isinstance(isometry_descriptor, Mapping):
                raise ValueError(
                    "lower_bound.xz_isometry must be an artifact descriptor"
                )
        else:
            raise ValueError(
                "lower_bound fields must be the legacy dual-sector schema or "
                "the proof-carrying X/Z-isometry extension"
            )
        if (
            type(lower["max_weight"]) is not int
            or lower["max_weight"] != policy["distance"] - 1
        ):
            failures.append("lower-bound threshold is not d-1")
        sectors = lower["sectors"]
        if not isinstance(sectors, list) or not all(
            isinstance(item, Mapping) for item in sectors
        ):
            raise ValueError("lower_bound.sectors must be a list of sector covers")
        by_sector = {
            item.get("sector"): item for item in sectors
        }
        if len(by_sector) != len(sectors):
            raise ValueError("lower-bound sector covers are duplicated")
        if isometry_descriptor is None:
            if len(sectors) != 2 or set(by_sector) != {"X", "Z"}:
                raise ValueError("legacy lower-bound sectors are not exactly X and Z")
            proof_sectors = ("X", "Z")
        else:
            if len(sectors) != 1 or set(by_sector) not in ({"X"}, {"Z"}):
                raise ValueError(
                    "isometric lower bound must carry exactly one X or Z proof sector"
                )
            proof_sectors = (next(iter(by_sector)),)
            _validate_xz_isometry_artifact(
                isometry_descriptor,
                root=root,
                hx=authoritative_hx,
                hz=authoritative_hz,
                supplied_proof_sector=proof_sectors[0],
            )
        covers = {by_sector[sector].get("cover") for sector in proof_sectors}
        if len(covers) != 1:
            raise ValueError("lower-bound proof sectors must use one common cover mode")
        selected_cover = next(iter(covers))
        symmetry = None
        symmetry_cubes: list[Mapping[str, Any]] | None = None
        if selected_cover == SYMMETRY_COVER:
            from scripts.screen_frontier_sat import build_anchor_cover_cubes

            symmetry = _construction_symmetry_report(
                top["construction"], hx, hz,
            )
            if not (
                symmetry.get("verified") is True
                and symmetry.get("orbits_cover_all_qubits") is True
                and symmetry.get("report_sha256")
                == canonical_sha256(symmetry, omit="report_sha256")
                and _strict_json_equal(lower["symmetry"], symmetry)
            ):
                raise ValueError("construction symmetry replay/binding failed")
            representatives = tuple(symmetry["orbit_representatives"])
            if sorted(
                qubit for orbit in symmetry["orbits"] for qubit in orbit
            ) != list(range(policy["n"])):
                raise ValueError("construction symmetry orbits are not complete")
            if any(orbit[0] != representative for orbit, representative in zip(
                symmetry["orbits"], representatives, strict=True,
            )):
                raise ValueError("construction symmetry representatives are not canonical")
            symmetry_cubes = build_anchor_cover_cubes(representatives)
        elif lower["symmetry"] is not None:
            raise ValueError("non-symmetry cover retained a symmetry report")
        for sector in proof_sectors:
            sector_label = f"lower_bound.{sector}"
            sector_cover = _exact_keys(
                by_sector[sector],
                {"sector", "cover", "units"},
                where=sector_label,
            )
            units = sector_cover["units"]
            if not isinstance(units, list) or not units or not all(
                isinstance(item, Mapping) for item in units
            ):
                raise ValueError(f"{sector_label}.units must be a nonempty list")
            if selected_cover == SYMMETRY_COVER:
                assert symmetry_cubes is not None
                partitions = _symmetry_unit_cover(units, symmetry_cubes)
            else:
                partitions = _expected_partition_indices(
                    cover=sector_cover["cover"],
                    k=policy["k"],
                    units=units,
                )
            for unit_index, (raw_record, partition_index) in enumerate(
                zip(units, partitions, strict=True)
            ):
                label = f"{sector_label}.units[{unit_index}]"
                record = _exact_keys(
                    raw_record,
                    {
                        "sector",
                        "partition_index",
                        "anchor_cube",
                        "formulation",
                        "formulation_revision",
                        "cardinality_encoding",
                        "check_matrix_sha256",
                        "target_logicals_sha256",
                        "cnf_sha256",
                        "num_variables",
                        "num_clauses",
                        "dimacs",
                        "proof_checks",
                    },
                    where=label,
                )
                checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
                expected_cube = (
                    symmetry_cubes[unit_index]
                    if symmetry_cubes is not None else None
                )
                if not _strict_json_equal(record["anchor_cube"], expected_cube):
                    failures.append(f"{label} symmetry anchor cube mismatch")
                cnf = build_css_threshold_cnf(
                    checks,
                    logicals,
                    max_weight=policy["distance"] - 1,
                    sector=sector,
                    cardinality_encoding="seqcounter",
                    partition_index=partition_index,
                    anchor_indices=(
                        None if expected_cube is None
                        else expected_cube["anchor_indices"]
                    ),
                    zero_anchor_indices=(
                        None if expected_cube is None
                        else expected_cube["zero_anchor_indices"]
                    ),
                    one_anchor_index=(
                        None if expected_cube is None
                        else expected_cube["one_anchor_index"]
                    ),
                    anchor_cube_sha256=(
                        None if expected_cube is None
                        else expected_cube["cube_sha256"]
                    ),
                )
                expected_metadata = {
                    "sector": sector,
                    "partition_index": partition_index,
                    "formulation": SAT_FORMULATION,
                    "formulation_revision": _FORMULATION_REVISION,
                    "cardinality_encoding": "seqcounter",
                    "check_matrix_sha256": _array_sha256("checks", checks),
                    "target_logicals_sha256": _array_sha256("logicals", logicals),
                    "cnf_sha256": cnf["cnf_sha256"],
                    "num_variables": cnf["num_variables"],
                    "num_clauses": cnf["num_clauses"],
                }
                if any(
                    type(record[key]) is not int
                    for key in ("num_variables", "num_clauses")
                ) or not _strict_json_equal(
                    {key: record[key] for key in expected_metadata},
                    expected_metadata,
                ):
                    failures.append(f"{label} CNF instance binding mismatch")
                with _open_pinned_artifact(
                    root,
                    record["dimacs"],
                    label=f"{label}.dimacs",
                    max_bytes=MAX_DIMACS_BYTES,
                ) as dimacs_stream:
                    if not _dimacs_matches(dimacs_stream, cnf):
                        failures.append(
                            f"{label} DIMACS does not reproduce byte-for-byte"
                        )
                    failures.extend(
                        _validate_dual_proof_checks(
                            record["proof_checks"],
                            root=root,
                            trusted_checkers=trusted_checkers,
                            dimacs_stream=dimacs_stream,
                            label=label,
                            checker_timeout_s=checker_timeout_s,
                        )
                    )
        upper = _exact_keys(proof["upper_bound"], {"witness"}, where="upper_bound")
        failures.extend(
            _validate_witness(
                upper["witness"],
                hx=hx,
                hz=hz,
                lx=lx,
                lz=lz,
                distance=policy["distance"],
            )
        )
    except (KeyError, OSError, StopIteration, TypeError, ValueError) as exc:
        failures.append(f"certificate validation incomplete: {exc}")

    valid = not failures
    return {
        "valid": valid,
        "proof_valid": valid,
        "calibration_valid": valid,
        # Generic certificate consumers interpret ``passed`` as release/win
        # acceptance, not merely mathematical replay validity.
        "passed": False,
        "win_awarded": False,
        "selected_win": False,
        "trusted_win": False,
        "formal_win": False,
        "failures": failures,
    }


def validate_exact_anchor_certificate(
    certificate: Mapping[str, Any],
    *,
    artifact_root: Path | str,
    trusted_checkers: Mapping[str, Mapping[str, Any]],
    checker_timeout_s: float,
) -> dict[str, Any]:
    """Validate the installed 2ebf... anchor as calibration, never as a win."""

    return _validate_certificate(
        certificate,
        artifact_root=artifact_root,
        trusted_checkers=trusted_checkers,
        checker_timeout_s=checker_timeout_s,
        policy=installed_anchor_policy(),
        authoritative_matrix_builder=_default_authoritative_matrices,
    )


__all__ = [
    "CERTIFICATE_ROLE",
    "CERTIFICATE_TYPE",
    "CHECKER_POLICY_KIND",
    "DRAT_CHECKER_ROLE",
    "GLOBAL_COVER",
    "LRAT_CHECKER_ROLE",
    "MAX_CHECKER_TIMEOUT_S",
    "MAX_TRUSTED_PROOF_BYTES",
    "MATRIX_BUNDLE_KIND",
    "PARTITION_COVER",
    "SCHEMA_VERSION",
    "SYMMETRY_COVER",
    "XZ_ISOMETRY_HASH_METHOD",
    "XZ_ISOMETRY_KIND",
    "build_exact_anchor_certificate",
    "build_xz_isometry_artifact",
    "canonical_sha256",
    "checker_semantic_stdout_sha256",
    "installed_anchor_policy",
    "load_trusted_checker_policy",
    "render_dimacs",
    "permutation_sha256",
    "seal_certificate",
    "validate_exact_anchor_certificate",
]
