"""Pure state helpers for resumable Stage 1 MILP audits.

This module deliberately has no controller or filesystem side effects.  It
classifies persisted evaluation rows, maintains JSON-serializable unresolved
entries, computes retry budgets, and reconstructs audit state from legacy
evaluation logs.  ``humanize.flow`` can adopt these helpers after its round
transaction work has landed.
"""

from __future__ import annotations

import copy
import hashlib
import json
import math
import os
import stat
import threading
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

from evaluation.geometry import candidate_geometry

from .state import code_key


AUDIT_STATE_VERSION = 1
AUDIT_ATTEMPT_VERSION = 2
LEGACY_AUDIT_ATTEMPT_VERSION = 1
UNRESOLVED_ENTRY_VERSION = 1
MAX_RETRY_MULTIPLIER = 4
_CSS_CHECKPOINT_KIND = "qcode-css-distance-milp-checkpoint"
_CSS_CHECKPOINT_SCHEMA_VERSION = 2
_SYMPLECTIC_CHECKPOINT_KIND = "qcode-symplectic-weight-checkpoint"
_SYMPLECTIC_CHECKPOINT_SCHEMA_VERSION = 1
_EVIDENCE_FIELDS = {
    "path",
    "sha256",
    "bytes",
    "checkpoint_kind",
    "checkpoint_schema_version",
    "checkpoint_status",
    "proof_binding_sha256",
}


class AuditStateError(ValueError):
    """Raised when persisted audit evidence is malformed or inconsistent."""


class AuditEvidenceImplementationMismatch(AuditStateError):
    """Immutable evidence was produced by another verifier implementation."""


class AuditOutcome(str, Enum):
    """Machine-derived disposition of one Stage 1 evaluation."""

    EXACT = "exact"
    THRESHOLD_REJECTED = "threshold_rejected"
    UNRESOLVED_NO_INCUMBENT = "unresolved_no_incumbent"
    UNRESOLVED_WINNER_NOT_EXCLUDED = "unresolved_winner_not_excluded"

    @property
    def terminal(self) -> bool:
        return self in {self.EXACT, self.THRESHOLD_REJECTED}

    @property
    def unresolved(self) -> bool:
        return not self.terminal


@dataclass(frozen=True)
class RetryBudget:
    """Effective solver budgets for one attempt."""

    multiplier: int
    timeout_per_logical: int
    total_timeout: int
    hard_timeout_per_logical: float | None


@dataclass(frozen=True)
class AuditAttempt:
    """Validated provenance for one completed solver attempt."""

    schema_version: int
    round_number: int
    kind: str
    attempt: int
    multiplier: int
    timeout_per_logical: int
    total_timeout: int
    hard_timeout_per_logical: float
    checkpoint_path: str
    candidate_key: str | None = None
    n: int | None = None
    k: int | None = None
    evidence: dict[str, Any] | None = None


@dataclass(frozen=True)
class RebuiltAuditState:
    """Terminal and unresolved state reconstructed from evaluation history."""

    terminal_keys: frozenset[str]
    terminal_digests: frozenset[str]
    unresolved: dict[str, dict[str, Any]]
    evaluations_seen: int

    def as_state_fields(self) -> dict[str, Any]:
        return {
            "audit_state_version": AUDIT_STATE_VERSION,
            "audited_keys": sorted(self.terminal_keys),
            "audited_structural_digests": sorted(self.terminal_digests),
            "unresolved_candidates": copy.deepcopy(self.unresolved),
        }


@dataclass(frozen=True)
class _FormalCheckpointValidation:
    checkpoint: dict[str, Any]
    exact_replay_verified: bool


FullyExact = Callable[[Mapping[str, Any]], bool]
CheckpointPathFor = Callable[[str], str | Path | None]


_EXACT_REPLAY_CACHE: dict[
    tuple[str, str, str, int, int, float],
    bool,
] = {}
_EXACT_REPLAY_CACHE_LOCK = threading.Lock()


def _strict_int(
    value: Any,
    label: str,
    *,
    minimum: int | None = None,
) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise AuditStateError(f"{label} must be an integer")
    if minimum is not None and value < minimum:
        raise AuditStateError(f"{label} must be >= {minimum}")
    return value


def _optional_bool(row: Mapping[str, Any], name: str) -> bool:
    value = row.get(name, False)
    if not isinstance(value, bool):
        raise AuditStateError(f"{name} must be boolean when present")
    return value


def _canonical_json(value: Any, label: str) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise AuditStateError(f"{label} must be strict JSON data") from exc


def _canonical_sha256(value: Any, label: str) -> str:
    return hashlib.sha256(_canonical_json(value, label)).hexdigest()


def _lexical_absolute(value: str | Path, label: str) -> Path:
    if not isinstance(value, (str, Path)):
        raise AuditStateError(f"{label} must be a filesystem path")
    path = Path(os.path.abspath(os.fspath(value)))
    if ".." in path.parts:
        raise AuditStateError(f"{label} must be an absolute normalized path")
    return path


def _reject_symlink_components(path: Path, label: str) -> None:
    current = Path(path.anchor)
    for component in path.parts[1:]:
        current /= component
        try:
            mode = os.lstat(current).st_mode
        except FileNotFoundError:
            continue
        except OSError as exc:
            raise AuditStateError(f"cannot inspect {label}: {current}") from exc
        if stat.S_ISLNK(mode):
            raise AuditStateError(f"{label} may not contain symlinks: {current}")


def _read_regular_bytes(path: Path, label: str) -> bytes:
    _reject_symlink_components(path, label)
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        file_descriptor = os.open(path, flags)
    except OSError as exc:
        raise AuditStateError(f"{label} is not a safe regular file: {path}") from exc
    try:
        if not stat.S_ISREG(os.fstat(file_descriptor).st_mode):
            raise AuditStateError(
                f"{label} is not a safe regular file: {path}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(file_descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(file_descriptor)


def _strict_json_object(payload: bytes, label: str) -> dict[str, Any]:
    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number: {value}")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate JSON key: {key}")
            value[key] = item
        return value

    try:
        decoded = json.loads(
            payload.decode("utf-8"),
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicates,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise AuditStateError(f"{label} is not strict JSON") from exc
    if not isinstance(decoded, dict):
        raise AuditStateError(f"{label} root must be an object")
    return decoded


def _ensure_safe_directory(path: Path, label: str) -> None:
    current = Path(path.anchor)
    for component in path.parts[1:]:
        current /= component
        try:
            mode = os.lstat(current).st_mode
        except FileNotFoundError:
            try:
                os.mkdir(current, 0o700)
                mode = os.lstat(current).st_mode
            except OSError as exc:
                raise AuditStateError(
                    f"cannot create {label}: {current}"
                ) from exc
        except OSError as exc:
            raise AuditStateError(f"cannot inspect {label}: {current}") from exc
        if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
            raise AuditStateError(
                f"{label} must contain only real directories: {current}"
            )


def _write_content_addressed_snapshot(path: Path, payload: bytes) -> None:
    if path.exists():
        if _read_regular_bytes(path, "audit evidence snapshot") != payload:
            raise AuditStateError(
                "content-addressed audit evidence has inconsistent bytes"
            )
        return
    temporary = path.with_name(
        f".{path.name}.tmp-{os.getpid()}-{threading.get_ident()}"
    )
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_EXCL
        | os.O_CLOEXEC
        | os.O_NOFOLLOW
    )
    try:
        descriptor = os.open(temporary, flags, 0o600)
        try:
            offset = 0
            while offset < len(payload):
                offset += os.write(descriptor, payload[offset:])
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        if path.exists():
            if _read_regular_bytes(path, "audit evidence snapshot") != payload:
                raise AuditStateError(
                    "content-addressed audit evidence has inconsistent bytes"
                )
        else:
            os.replace(temporary, path)
            directory_descriptor = os.open(path.parent, os.O_RDONLY)
            try:
                os.fsync(directory_descriptor)
            finally:
                os.close(directory_descriptor)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _checkpoint_metadata(checkpoint: Mapping[str, Any]) -> tuple[str, int, str, str]:
    kind = checkpoint.get("kind")
    schema = checkpoint.get("schema_version")
    allowed = {
        (_CSS_CHECKPOINT_KIND, _CSS_CHECKPOINT_SCHEMA_VERSION),
        (_SYMPLECTIC_CHECKPOINT_KIND, _SYMPLECTIC_CHECKPOINT_SCHEMA_VERSION),
    }
    if (kind, schema) not in allowed:
        raise AuditStateError("unsupported Stage 1 checkpoint kind/schema")
    status = checkpoint.get("status")
    allowed_statuses = (
        {"exact", "threshold_rejected", "unresolved"}
        if kind == _CSS_CHECKPOINT_KIND
        else {"exact", "threshold_rejected"}
    )
    if not isinstance(status, str) or status not in allowed_statuses:
        raise AuditStateError("Stage 1 checkpoint status is invalid")
    proof_binding = checkpoint.get("proof_binding")
    if not isinstance(proof_binding, Mapping):
        raise AuditStateError("Stage 1 checkpoint proof_binding is missing")
    binding_sha256 = proof_binding.get("binding_sha256")
    if not isinstance(binding_sha256, str) or len(binding_sha256) != 64:
        raise AuditStateError("Stage 1 checkpoint proof binding hash is invalid")
    unsigned = dict(proof_binding)
    unsigned.pop("binding_sha256", None)
    if _canonical_sha256(unsigned, "checkpoint proof_binding") != binding_sha256:
        raise AuditStateError("Stage 1 checkpoint proof_binding hash mismatch")
    return str(kind), int(schema), status, binding_sha256


def seal_audit_attempt_evidence(
    row: Mapping[str, Any],
    attempt: Mapping[str, Any],
    *,
    run_dir: str | Path,
    evidence_root: str | Path,
) -> dict[str, Any]:
    """Freeze a working checkpoint and return a complete schema-v2 attempt.

    Flow must call this after the evaluator has returned and candidate identity
    fields have been restored, but before the row enters the canonical JSONL.
    """
    if not isinstance(row, Mapping) or not isinstance(attempt, Mapping):
        raise AuditStateError("audit row and attempt must be objects")
    key, _digest, _candidate = _candidate_snapshot(row)
    n = _strict_int(row.get("n"), "n", minimum=1)
    k = _strict_int(row.get("k"), "k", minimum=1)
    base_fields = {
        "schema_version",
        "round",
        "kind",
        "attempt",
        "multiplier",
        "soft",
        "total",
        "hard",
        "checkpoint",
    }
    if set(attempt) != base_fields:
        raise AuditStateError("unsealed audit_attempt fields are invalid")
    unsealed = dict(attempt)
    unsealed["schema_version"] = LEGACY_AUDIT_ATTEMPT_VERSION
    parsed = _audit_attempt({"audit_attempt": unsealed})
    assert parsed is not None

    run_root = _lexical_absolute(run_dir, "run_dir")
    evidence = _lexical_absolute(evidence_root, "evidence_root")
    working = _lexical_absolute(parsed.checkpoint_path, "working checkpoint")
    expected_checkpoint_root = run_root / "milp-checkpoints"
    if working != expected_checkpoint_root / f"{key}.json":
        raise AuditStateError(
            "working checkpoint is not the candidate-bound run checkpoint"
        )
    if evidence != expected_checkpoint_root / "evidence":
        raise AuditStateError(
            "evidence_root must be run_dir/milp-checkpoints/evidence"
        )
    _reject_symlink_components(run_root, "run directory")
    payload = _read_regular_bytes(working, "working checkpoint")
    checkpoint = _strict_json_object(payload, "working checkpoint")
    checkpoint_kind, checkpoint_schema, checkpoint_status, binding_sha = (
        _checkpoint_metadata(checkpoint)
    )

    digest = hashlib.sha256(payload).hexdigest()
    candidate_root = evidence / key
    _ensure_safe_directory(candidate_root, "audit evidence directory")
    snapshot = candidate_root / f"{digest}.json"
    _write_content_addressed_snapshot(snapshot, payload)
    descriptor = {
        "path": str(snapshot),
        "sha256": digest,
        "bytes": len(payload),
        "checkpoint_kind": checkpoint_kind,
        "checkpoint_schema_version": checkpoint_schema,
        "checkpoint_status": checkpoint_status,
        "proof_binding_sha256": binding_sha,
    }
    sealed = dict(unsealed)
    sealed.update({
        "schema_version": AUDIT_ATTEMPT_VERSION,
        "candidate_key": key,
        "n": n,
        "k": k,
        "evidence": descriptor,
    })
    # Full validation here makes the caller fail before committing canonical
    # state, rather than discovering malformed evidence only on next resume.
    _validated_formal_checkpoint(
        row,
        _audit_attempt({"audit_attempt": sealed}),
        verify_exact=False,
    )
    return sealed


def is_fully_exact(row: Mapping[str, Any]) -> bool:
    """Return exactness from one strict, replayable machine predicate."""
    d_is_exact = _optional_bool(row, "d_is_exact")
    stage = row.get("stage")
    if stage is not None and not isinstance(stage, str):
        raise AuditStateError("stage must be a string when present")
    distance = None
    if d_is_exact:
        distance = _strict_int(row.get("d"), "d", minimum=1)

    if d_is_exact and stage in {"self_dual_d2", "symplectic_low_d"}:
        return distance == 2

    details = row.get("milp_details")
    if details is None:
        return d_is_exact and stage == "exact"
    if not isinstance(details, Mapping):
        raise AuditStateError("milp_details must be an object")
    exact = details.get("exact", False)
    if not isinstance(exact, bool):
        raise AuditStateError("milp_details.exact must be boolean")
    if not exact:
        return False

    total = _strict_int(
        details.get("total_logicals"), "milp_details.total_logicals", minimum=1
    )
    checked = _strict_int(
        details.get("num_logicals_checked"),
        "milp_details.num_logicals_checked",
        minimum=0,
    )
    optimal = _strict_int(
        details.get("logicals_optimal"),
        "milp_details.logicals_optimal",
        minimum=0,
    )
    return d_is_exact and checked == total == optimal


def _fraction_from_target(row: Mapping[str, Any]) -> Fraction:
    numerator = _strict_int(
        row.get("fom_target_numerator"),
        "fom_target_numerator",
        minimum=0,
    )
    denominator = _strict_int(
        row.get("fom_target_denominator"),
        "fom_target_denominator",
        minimum=1,
    )
    target = Fraction(numerator, denominator)
    target_value = row.get("fom_target")
    if isinstance(target_value, bool) or not isinstance(
        target_value, (int, float, str)
    ):
        raise AuditStateError("fom_target must be a finite numeric value")
    try:
        reported = Fraction(str(target_value))
    except (ValueError, ZeroDivisionError) as exc:
        raise AuditStateError("fom_target must be a finite numeric value") from exc
    if reported != target:
        raise AuditStateError("fom_target does not match its exact rational fields")
    return target


def _validate_reported_distance_metrics(
    row: Mapping[str, Any],
    *,
    n: int,
    k: int,
) -> None:
    """Bind ranking fields to the machine-replayed integer parameters."""

    distance = _strict_int(row.get("d"), "d", minimum=0)
    expected_fom = k * distance * distance / n
    exact = (
        row.get("d_is_exact") is True
        and row.get("distance_status") == "exact"
    )
    for field, expected in (
        ("fom", expected_fom),
        # Upper-bound FOM remains a diagnostic, but positive search score is
        # reserved for exact evidence.
        ("score", expected_fom if exact else 0.0),
        ("encoding_rate", k / n),
    ):
        if field not in row:
            continue
        observed = row[field]
        if (
            isinstance(observed, bool)
            or not isinstance(observed, (int, float))
            or not math.isfinite(float(observed))
            or not math.isclose(
                float(observed),
                float(expected),
                rel_tol=1e-12,
                abs_tol=1e-12,
            )
        ):
            raise AuditStateError(
                f"{field} disagrees with the replayed n/k/d values"
            )


def _challenge_cutoff(n: int, k: int, target: Fraction) -> tuple[int, int]:
    scalar = math.isqrt((target.numerator * n) // (target.denominator * k))
    from evaluation.final_gate import FOM_THRESHOLD, minimum_winning_distance

    if target != Fraction(str(FOM_THRESHOLD)):
        return scalar, scalar
    try:
        minimum_passing = minimum_winning_distance(n, k)
    except ValueError:
        challenge = min(scalar, n)
    else:
        challenge = min(scalar, minimum_passing - 1)
    return scalar, challenge


def _verified_legacy_threshold_rejection(row: Mapping[str, Any]) -> bool:
    """Replay narrowly-scoped pre-threshold-flag upper-bound evidence."""
    if row.get("distance_trusted") is not True:
        return False
    n = _strict_int(row.get("n"), "n", minimum=1)
    k = _strict_int(row.get("k"), "k", minimum=1)
    distance = _strict_int(row.get("d"), "d", minimum=1)

    from evaluation.final_gate import FOM_THRESHOLD

    _scalar, challenge = _challenge_cutoff(
        n,
        k,
        Fraction(str(FOM_THRESHOLD)),
    )
    if distance > challenge:
        return False

    if row.get("stage") == "symplectic_low_d":
        symplectic = row.get("d_symplectic")
        if isinstance(symplectic, bool) or not isinstance(symplectic, int):
            return False
        return symplectic == distance

    if (
        row.get("milp_attempted") is not True
        or row.get("distance_source") != "milp_incumbent"
    ):
        return False
    details = row.get("milp_details")
    if not isinstance(details, Mapping):
        return False
    if _optional_bool(details, "all_timeout") or _optional_bool(
        details, "no_incumbent"
    ):
        return False
    if row.get("distance_status") in {
        "unknown",
        "unknown_no_incumbent",
        "hard_timeout",
    }:
        return False
    incumbents = details.get("logicals_incumbent")
    optimal = details.get("logicals_optimal")
    if (
        isinstance(incumbents, bool)
        or not isinstance(incumbents, int)
        or incumbents < 0
        or isinstance(optimal, bool)
        or not isinstance(optimal, int)
        or optimal < 0
        or incumbents + optimal < 1
    ):
        return False
    witnesses = []
    for name in ("d_x", "d_z"):
        value = details.get(name)
        if isinstance(value, bool) or not isinstance(value, int):
            return False
        if value > 0:
            witnesses.append(value)
    return bool(witnesses) and min(witnesses) == distance


def _positive_direction_distance(
    details: Mapping[str, Any], proof_distance: int
) -> None:
    positive: list[int] = []
    for name in ("d_x", "d_z"):
        value = _strict_int(
            details.get(name), f"milp_details.{name}", minimum=0
        )
        if value > 0:
            positive.append(value)
    if not positive:
        raise AuditStateError(
            "MILP feasible threshold proof has no positive direction distance"
        )
    if min(positive) != proof_distance:
        raise AuditStateError(
            "MILP direction distances disagree with threshold_proof_distance"
        )


def _replay_embedded_direction_witness(
    row: Mapping[str, Any],
    details: Mapping[str, Any],
    proof_distance: int,
) -> None:
    raw = row.get("threshold_proof_witness")
    if not isinstance(raw, Mapping):
        raise AuditStateError(
            "explicit MILP threshold proof requires threshold_proof_witness"
        )
    required = {"side", "index", "weight", "bits"}
    if set(raw) != required:
        raise AuditStateError(
            "threshold_proof_witness fields are invalid"
        )
    embedded = details.get("minimum_direction_witness")
    if not isinstance(embedded, Mapping) or dict(embedded) != dict(raw):
        raise AuditStateError(
            "threshold proof witness disagrees with milp_details"
        )

    side = raw.get("side")
    if side not in {"X", "Z"}:
        raise AuditStateError("threshold proof witness side must be X or Z")
    index = _strict_int(
        raw.get("index"), "threshold_proof_witness.index", minimum=0
    )
    weight = _strict_int(
        raw.get("weight"), "threshold_proof_witness.weight", minimum=1
    )
    if weight != proof_distance:
        raise AuditStateError(
            "threshold proof witness weight disagrees with proof distance"
        )
    raw_bits = raw.get("bits")
    if not isinstance(raw_bits, list):
        raise AuditStateError("threshold proof witness bits must be a list")
    bits = [
        _strict_int(
            bit, f"threshold_proof_witness.bits[{offset}]", minimum=0
        )
        for offset, bit in enumerate(raw_bits)
    ]
    if any(bit not in {0, 1} for bit in bits):
        raise AuditStateError("threshold proof witness bits must be binary")

    ell = _strict_int(row.get("ell"), "ell", minimum=1)
    m = _strict_int(row.get("m"), "m", minimum=1)
    a_terms = [
        tuple(term) for term in _normalise_terms(row.get("A_terms"), "A_terms")
    ]
    b_terms = [
        tuple(term) for term in _normalise_terms(row.get("B_terms"), "B_terms")
    ]
    try:
        from evaluation.bb_code import build_bb_code
        from evaluation.distance_milp import (
            get_code_matrices,
            replay_css_direction_witness,
        )

        code = build_bb_code(
            ell, m, a_terms, b_terms, geometry=candidate_geometry(row),
        )
        n = _strict_int(row.get("n"), "n", minimum=1)
        k = _strict_int(row.get("k"), "k", minimum=1)
        if int(code.num_qudits) != n or int(code.dimension) != k:
            raise AuditStateError(
                "threshold proof candidate dimensions do not match n/k"
            )
        hx, hz, lx, lz = get_code_matrices(code)
        logicals = lx if side == "Z" else lz
        checks = hx if side == "Z" else hz
        if index >= len(logicals):
            raise AuditStateError(
                "threshold proof witness logical index is out of range"
            )
        replayed = replay_css_direction_witness(
            checks, logicals[index], weight, bits
        )
        if replayed != bits:
            raise AuditStateError(
                "threshold proof witness is not canonically binary"
            )
    except AuditStateError:
        raise
    except Exception as exc:
        raise AuditStateError(
            "threshold proof witness failed matrix/parity replay"
        ) from exc


def _rebuild_candidate_code(
    row: Mapping[str, Any],
) -> tuple[Any, Any, Any, Any, Any]:
    ell = _strict_int(row.get("ell"), "ell", minimum=1)
    m = _strict_int(row.get("m"), "m", minimum=1)
    a_terms = [
        tuple(term) for term in _normalise_terms(row.get("A_terms"), "A_terms")
    ]
    b_terms = [
        tuple(term) for term in _normalise_terms(row.get("B_terms"), "B_terms")
    ]
    try:
        from evaluation.bb_code import build_bb_code
        from evaluation.distance_milp import get_code_matrices

        code = build_bb_code(
            ell, m, a_terms, b_terms, geometry=candidate_geometry(row),
        )
        hx, hz, lx, lz = get_code_matrices(code)
    except Exception as exc:
        raise AuditStateError(
            "formal Stage 1 evidence candidate reconstruction failed"
        ) from exc
    n = _strict_int(row.get("n"), "n", minimum=1)
    k = _strict_int(row.get("k"), "k", minimum=1)
    if int(code.num_qudits) != n or int(code.dimension) != k:
        raise AuditStateError(
            "formal Stage 1 evidence candidate dimensions do not match n/k"
        )
    return code, hx, hz, lx, lz


def _validate_formal_invocation(
    row: Mapping[str, Any],
    attempt: AuditAttempt,
) -> None:
    raw = row.get("audit_evaluator_invocation")
    required = {
        "schema_version",
        "checkpoint_path",
        "resume",
        "timeout_per_logical",
        "total_timeout",
        "hard_timeout_per_logical",
    }
    if not isinstance(raw, Mapping) or set(raw) != required:
        raise AuditStateError(
            "formal terminal evidence requires evaluator invocation schema 2"
        )
    if raw.get("schema_version") != AUDIT_ATTEMPT_VERSION:
        raise AuditStateError("evaluator invocation schema_version is invalid")
    if raw.get("checkpoint_path") != attempt.checkpoint_path:
        raise AuditStateError("evaluator invocation checkpoint path mismatch")
    if raw.get("resume") is not True:
        raise AuditStateError("formal evaluator invocation must enable resume")
    soft = _strict_int(
        raw.get("timeout_per_logical"),
        "audit_evaluator_invocation.timeout_per_logical",
        minimum=1,
    )
    total = _strict_int(
        raw.get("total_timeout"),
        "audit_evaluator_invocation.total_timeout",
        minimum=1,
    )
    hard = raw.get("hard_timeout_per_logical")
    if (
        isinstance(hard, bool)
        or not isinstance(hard, (int, float))
        or not math.isfinite(float(hard))
        or float(hard) <= 0
    ):
        raise AuditStateError(
            "evaluator invocation hard timeout is invalid"
        )
    if (
        soft != attempt.timeout_per_logical
        or total != attempt.total_timeout
        or not math.isclose(
            float(hard),
            attempt.hard_timeout_per_logical,
            rel_tol=0.0,
            abs_tol=1e-9,
        )
    ):
        raise AuditStateError("evaluator invocation budget binding mismatch")


def _validate_checkpoint_run_parameters(
    row: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    attempt: AuditAttempt,
) -> None:
    parameters = checkpoint.get("run_parameters")
    required = {
        "timeout_per_logical_s",
        "total_timeout_s",
        "hard_timeout_per_logical_s",
        "early_stop",
    }
    if not isinstance(parameters, Mapping) or set(parameters) != required:
        raise AuditStateError("checkpoint run_parameters are invalid")
    expected = (
        float(attempt.timeout_per_logical),
        float(attempt.total_timeout),
        float(attempt.hard_timeout_per_logical),
    )
    observed = (
        parameters.get("timeout_per_logical_s"),
        parameters.get("total_timeout_s"),
        parameters.get("hard_timeout_per_logical_s"),
    )
    for index, value in enumerate(observed):
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(float(value))
            or not math.isclose(
                float(value), expected[index], rel_tol=0.0, abs_tol=1e-9
            )
        ):
            raise AuditStateError("checkpoint budget binding mismatch")
    early_stop = row.get("milp_effective_early_stop")
    if early_stop is not None:
        early_stop = _strict_int(
            early_stop, "milp_effective_early_stop", minimum=0
        )
    if parameters.get("early_stop") != early_stop:
        raise AuditStateError("checkpoint early_stop binding mismatch")


def _validate_css_checkpoint_replay(
    row: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    code: Any,
    hx: Any,
    hz: Any,
    lx: Any,
    lz: Any,
) -> bool:
    try:
        from evaluation.distance_milp import (
            _binary_array_sha256,
            replay_css_direction_witness,
        )
    except Exception as exc:
        raise AuditStateError("cannot load CSS witness verifier") from exc
    k = int(code.dimension)
    n = int(code.num_qudits)
    expected_solver = {
        "backend": "scipy.optimize.milp-highs",
        "formulation": "css-logical-parity",
        "formulation_revision": "css-logical-parity-binary-witness-v2",
        "objective": "hamming_weight",
        "presolve": True,
    }
    if checkpoint["proof_binding"].get("solver") != expected_solver:
        raise AuditStateError("CSS checkpoint solver binding mismatch")
    expected_definitions: list[dict[str, Any]] = []
    for side, logicals, checks in (("Z", lx, hx), ("X", lz, hz)):
        check_sha = _binary_array_sha256(f"{side}-checks", checks)
        for index in range(k):
            expected_definitions.append({
                "direction_id": f"{side}:{index}",
                "side": side,
                "index": index,
                "check_matrix_sha256": check_sha,
                "logical_sha256": _binary_array_sha256(
                    f"{side}-logical-{index}", logicals[index]
                ),
            })
    binding = checkpoint["proof_binding"]
    if binding.get("directions") != expected_definitions:
        raise AuditStateError("checkpoint logical directions mismatch")
    if binding.get("directions_sha256") != _canonical_sha256(
        expected_definitions, "logical directions"
    ):
        raise AuditStateError("checkpoint logical direction hash mismatch")
    definitions = {
        definition["direction_id"]: definition
        for definition in expected_definitions
    }
    records = checkpoint.get("direction_results")
    if not isinstance(records, Mapping):
        raise AuditStateError("CSS checkpoint direction_results are invalid")
    if any(direction_id not in definitions for direction_id in records):
        raise AuditStateError("CSS checkpoint contains an unknown direction")
    feasible: list[tuple[int, int, int, dict[str, Any]]] = []
    optimal = incumbent = 0
    for direction_id, raw_record in records.items():
        if not isinstance(raw_record, Mapping):
            raise AuditStateError("CSS checkpoint direction record is invalid")
        definition = definitions[direction_id]
        side = definition["side"]
        index = definition["index"]
        if (
            raw_record.get("side") != side
            or raw_record.get("index") != index
            or raw_record.get("logical_sha256")
            != definition["logical_sha256"]
        ):
            raise AuditStateError("CSS checkpoint direction binding mismatch")
        status = raw_record.get("status")
        if status not in {
            "optimal",
            "incumbent",
            "no_incumbent",
            "hard_timeout",
        }:
            raise AuditStateError("CSS checkpoint direction status is invalid")
        weight = raw_record.get("weight")
        witness = raw_record.get("witness")
        if status in {"optimal", "incumbent"}:
            weight = _strict_int(
                weight, f"direction_results.{direction_id}.weight", minimum=1
            )
            if weight > n:
                raise AuditStateError("CSS checkpoint witness weight exceeds n")
            checks = hx if side == "Z" else hz
            logical = lx[index] if side == "Z" else lz[index]
            try:
                bits = replay_css_direction_witness(
                    checks, logical, weight, witness
                )
            except Exception as exc:
                raise AuditStateError(
                    "CSS checkpoint direction witness replay failed"
                ) from exc
            proof = {
                "side": side,
                "index": index,
                "weight": weight,
                "bits": bits,
            }
            feasible.append(
                (weight, 0 if side == "Z" else 1, index, proof)
            )
            optimal += status == "optimal"
            incumbent += status == "incumbent"
        elif weight is not None or witness is not None:
            raise AuditStateError(
                "unresolved CSS direction retained feasible evidence"
            )
    minimum_witness = (
        min(feasible, key=lambda item: item[:3])[-1] if feasible else None
    )
    details = row.get("milp_details")
    if not isinstance(details, Mapping):
        raise AuditStateError("formal CSS evidence requires milp_details")
    expected_counts = {
        "num_logicals_checked": len(records),
        "logicals_optimal": optimal,
        "logicals_incumbent": incumbent,
        "total_logicals": 2 * k,
    }
    for field, expected in expected_counts.items():
        if _strict_int(
            details.get(field), f"milp_details.{field}", minimum=0
        ) != expected:
            raise AuditStateError(f"milp_details.{field} disagrees with evidence")
    evidence_exact = optimal == 2 * k and len(records) == 2 * k
    if details.get("exact") is not evidence_exact:
        raise AuditStateError("milp_details.exact disagrees with checkpoint")
    if row.get("d_is_exact") is not evidence_exact:
        raise AuditStateError("d_is_exact disagrees with checkpoint")
    if evidence_exact and checkpoint.get("status") != "exact":
        raise AuditStateError("all-optimal CSS evidence is not status=exact")
    if not evidence_exact and checkpoint.get("status") == "exact":
        raise AuditStateError("checkpoint exact status lacks all directions")
    if feasible:
        proof_distance = min(item[0] for item in feasible)
        if evidence_exact:
            if _strict_int(row.get("d"), "d", minimum=1) != proof_distance:
                raise AuditStateError(
                    "exact row distance disagrees with checkpoint witnesses"
                )
        elif row.get("threshold_rejection_proven") is True:
            if _strict_int(
                row.get("threshold_proof_distance"),
                "threshold_proof_distance",
                minimum=1,
            ) != proof_distance:
                raise AuditStateError(
                    "threshold distance disagrees with checkpoint witnesses"
                )
        elif (
            row.get("distance_source") in {None, "milp_incumbent"}
            and _strict_int(row.get("d"), "d", minimum=1) != proof_distance
        ):
            raise AuditStateError(
                "MILP row distance disagrees with checkpoint witnesses"
            )
    elif row.get("distance_status") not in {
        "unknown",
        "unknown_no_incumbent",
        "hard_timeout",
    }:
        raise AuditStateError("checkpoint has no feasible distance witness")
    if details.get("minimum_direction_witness") != minimum_witness:
        raise AuditStateError(
            "milp_details minimum witness disagrees with checkpoint"
        )
    if row.get("threshold_rejection_proven") is True:
        if row.get("threshold_proof_witness") != minimum_witness:
            raise AuditStateError(
                "threshold witness disagrees with checkpoint minimum"
            )
    return evidence_exact


def _validate_symplectic_checkpoint_replay(
    row: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    code: Any,
) -> bool:
    raw = checkpoint.get("symplectic_witness")
    if not isinstance(raw, Mapping):
        raise AuditStateError("symplectic checkpoint witness is missing")
    try:
        from evaluation.distance_milp import symplectic_weight_witness

        replayed = symplectic_weight_witness(code, raw.get("weight"))
    except Exception as exc:
        raise AuditStateError("symplectic witness replay failed") from exc
    if replayed is None or replayed != dict(raw):
        raise AuditStateError(
            "symplectic witness logical/dual replay mismatch"
        )
    binding = checkpoint["proof_binding"]
    if binding.get("method") != "logical-basis-symplectic-upper-bound":
        raise AuditStateError("symplectic checkpoint method binding mismatch")
    if binding.get("witness_sha256") != _canonical_sha256(
        dict(raw), "symplectic witness"
    ):
        raise AuditStateError("symplectic checkpoint witness hash mismatch")
    weight = _strict_int(raw.get("weight"), "symplectic witness weight", minimum=1)
    if _strict_int(
        row.get("d_symplectic"), "d_symplectic", minimum=1
    ) != weight:
        raise AuditStateError("symplectic witness distance mismatch")
    if row.get("symplectic_weight_witness") != dict(raw):
        raise AuditStateError("row symplectic witness disagrees with checkpoint")
    if row.get("threshold_rejection_proven") is True:
        if _strict_int(
            row.get("threshold_proof_distance"),
            "threshold_proof_distance",
            minimum=1,
        ) != weight:
            raise AuditStateError(
                "symplectic threshold distance disagrees with checkpoint"
            )
        if row.get("threshold_proof_witness") != dict(raw):
            raise AuditStateError(
                "threshold symplectic witness disagrees with checkpoint"
            )
    exact = weight <= 2
    if row.get("d_is_exact") is not exact:
        raise AuditStateError("symplectic exactness disagrees with its weight")
    if exact and _strict_int(row.get("d"), "d", minimum=1) != weight:
        raise AuditStateError("exact symplectic row distance mismatch")
    expected_status = "exact" if exact else "threshold_rejected"
    if checkpoint.get("status") != expected_status:
        raise AuditStateError("symplectic checkpoint status mismatch")
    return exact


def _independently_replay_css_exact(
    *,
    code: Any,
    checkpoint: Mapping[str, Any],
    attempt: AuditAttempt,
    evidence_sha256: str,
) -> bool:
    """Freshly establish every CSS lower bound without trusting stored status."""

    try:
        from evaluation.distance_milp import (
            _implementation_fingerprint,
            replay_css_exact_directions,
        )

        implementation_sha256 = _implementation_fingerprint().get(
            "fingerprint_sha256"
        )
    except Exception:
        # A verifier outage is operationally unresolved, never exact.
        return False
    if not isinstance(implementation_sha256, str):
        raise AuditStateError("CSS exact replay implementation is unbound")
    binding = checkpoint.get("proof_binding")
    if not isinstance(binding, Mapping):
        raise AuditStateError("CSS exact replay proof binding is missing")
    matrix_sha256 = binding.get("matrix_bundle_sha256")
    if not isinstance(matrix_sha256, str):
        raise AuditStateError("CSS exact replay matrix binding is invalid")
    if attempt.total_timeout % attempt.multiplier:
        raise AuditStateError(
            "CSS exact replay total budget is not a multiplier scale"
        )
    base_total_timeout = attempt.total_timeout // attempt.multiplier
    cumulative_multiplier = sum(
        min(1 << min(index, 2), MAX_RETRY_MULTIPLIER)
        for index in range(attempt.attempt)
    )
    replay_total_timeout = base_total_timeout * cumulative_multiplier
    cache_key = (
        evidence_sha256,
        implementation_sha256,
        matrix_sha256,
        attempt.timeout_per_logical,
        replay_total_timeout,
        attempt.hard_timeout_per_logical,
    )
    with _EXACT_REPLAY_CACHE_LOCK:
        if cache_key in _EXACT_REPLAY_CACHE:
            return _EXACT_REPLAY_CACHE[cache_key]

    try:
        replay = replay_css_exact_directions(
            code,
            checkpoint.get("direction_results"),
            timeout_per_logical=attempt.timeout_per_logical,
            # A completed checkpoint may have accumulated optimal directions
            # across 1x/2x/4x retries. Replaying all 2k directions from zero
            # therefore receives the same cumulative wall budget, while each
            # individual direction remains capped by the current attempt.
            total_timeout=replay_total_timeout,
            hard_timeout_per_logical=attempt.hard_timeout_per_logical,
        )
    except Exception:
        return False
    status = getattr(replay, "status", None)
    if status == "unavailable":
        return False
    if status == "mismatch":
        direction = getattr(replay, "direction_id", None)
        reason = getattr(replay, "reason", "unknown")
        expected = getattr(replay, "expected_weight", None)
        observed = getattr(replay, "observed_weight", None)
        raise AuditStateError(
            "CSS exact replay mismatch: "
            f"reason={reason}, direction={direction}, "
            f"stored={expected}, replayed={observed}"
        )
    if status != "exact":
        raise AuditStateError("CSS exact replay returned an invalid status")
    total = 2 * int(code.dimension)
    if (
        getattr(replay, "checked_directions", None) != total
        or getattr(replay, "total_directions", None) != total
    ):
        raise AuditStateError(
            "CSS exact replay did not prove every logical direction"
        )
    with _EXACT_REPLAY_CACHE_LOCK:
        _EXACT_REPLAY_CACHE[cache_key] = True
    return True


def _validated_formal_checkpoint(
    row: Mapping[str, Any],
    attempt: AuditAttempt | None,
    *,
    verify_exact: bool = True,
) -> _FormalCheckpointValidation | None:
    if attempt is None or attempt.schema_version < AUDIT_ATTEMPT_VERSION:
        return None
    assert attempt.evidence is not None
    key, _digest, _candidate = _candidate_snapshot(row)
    n = _strict_int(row.get("n"), "n", minimum=1)
    k = _strict_int(row.get("k"), "k", minimum=1)
    _validate_reported_distance_metrics(row, n=n, k=k)
    if (
        attempt.candidate_key != key
        or attempt.n != n
        or attempt.k != k
    ):
        raise AuditStateError("audit_attempt candidate/n/k binding mismatch")
    _validate_formal_invocation(row, attempt)

    descriptor = attempt.evidence
    digest = descriptor.get("sha256")
    if (
        not isinstance(digest, str)
        or len(digest) != 64
        or any(character not in "0123456789abcdef" for character in digest)
    ):
        raise AuditStateError("audit evidence sha256 is invalid")
    byte_count = _strict_int(
        descriptor.get("bytes"), "audit evidence bytes", minimum=1
    )
    working = _lexical_absolute(
        attempt.checkpoint_path, "working checkpoint"
    )
    if working.name != f"{key}.json":
        raise AuditStateError(
            "working checkpoint filename is not candidate-bound"
        )
    snapshot = _lexical_absolute(
        descriptor.get("path"), "audit evidence path"
    )
    expected = (
        working.parent
        / "evidence"
        / key
        / f"{digest}.json"
    )
    if snapshot != expected:
        raise AuditStateError(
            "audit evidence path is not content-addressed for the candidate"
        )
    payload = _read_regular_bytes(snapshot, "audit evidence snapshot")
    if len(payload) != byte_count:
        raise AuditStateError("audit evidence byte count mismatch")
    if hashlib.sha256(payload).hexdigest() != digest:
        raise AuditStateError("audit evidence sha256 mismatch")
    checkpoint = _strict_json_object(payload, "audit evidence snapshot")
    kind, schema, status, binding_sha = _checkpoint_metadata(checkpoint)
    expected_metadata = {
        "checkpoint_kind": kind,
        "checkpoint_schema_version": schema,
        "checkpoint_status": status,
        "proof_binding_sha256": binding_sha,
    }
    for field, expected_value in expected_metadata.items():
        if descriptor.get(field) != expected_value:
            raise AuditStateError(f"audit evidence {field} mismatch")

    binding = checkpoint["proof_binding"]
    expected_identity = {
        "family": "css-bb",
        "ell": _strict_int(row.get("ell"), "ell", minimum=1),
        "m": _strict_int(row.get("m"), "m", minimum=1),
        "A_terms": _normalise_terms(row.get("A_terms"), "A_terms"),
        "B_terms": _normalise_terms(row.get("B_terms"), "B_terms"),
    }
    geometry = candidate_geometry(row)
    if geometry is not None:
        expected_identity["geometry"] = geometry
    if binding.get("candidate_identity") != expected_identity:
        raise AuditStateError("checkpoint candidate identity mismatch")
    if binding.get("n") != n or binding.get("k") != k:
        raise AuditStateError("checkpoint n/k binding mismatch")

    code, hx, hz, lx, lz = _rebuild_candidate_code(row)
    try:
        from evaluation.distance_milp import (
            _implementation_fingerprint,
            _matrix_bundle_sha256,
        )

        current_implementation = _implementation_fingerprint()
        matrix_sha = _matrix_bundle_sha256(hx, hz, lx, lz)
    except Exception as exc:
        raise AuditStateError("cannot fingerprint Stage 1 verifier") from exc
    if binding.get("implementation") != current_implementation:
        raise AuditEvidenceImplementationMismatch(
            "checkpoint implementation fingerprint mismatch"
        )
    if binding.get("matrix_bundle_sha256") != matrix_sha:
        raise AuditStateError("checkpoint reconstructed matrix hash mismatch")
    _validate_checkpoint_run_parameters(row, checkpoint, attempt)
    details = row.get("milp_details")
    if not isinstance(details, Mapping):
        raise AuditStateError("formal Stage 1 evidence requires milp_details")
    if details.get("checkpoint_path") != attempt.checkpoint_path:
        raise AuditStateError("milp_details working checkpoint path mismatch")
    if details.get("checkpoint_status") != status:
        raise AuditStateError("milp_details checkpoint status mismatch")
    exact_replay_verified = False
    if kind == _CSS_CHECKPOINT_KIND:
        evidence_exact = _validate_css_checkpoint_replay(
            row, checkpoint, code, hx, hz, lx, lz
        )
        if evidence_exact and verify_exact:
            exact_replay_verified = _independently_replay_css_exact(
                code=code,
                checkpoint=checkpoint,
                attempt=attempt,
                evidence_sha256=digest,
            )
    else:
        exact_replay_verified = _validate_symplectic_checkpoint_replay(
            row, checkpoint, code
        )
    return _FormalCheckpointValidation(
        checkpoint=dict(checkpoint),
        exact_replay_verified=exact_replay_verified,
    )


def _verified_threshold_rejection(
    row: Mapping[str, Any],
    *,
    fully_exact: bool,
    formal_checkpoint: Mapping[str, Any] | None,
) -> bool:
    # Schema 0/1 rows predate immutable checkpoint evidence.  Their numeric
    # claims are retained for retry scheduling but can never become terminal.
    if formal_checkpoint is None:
        return False
    if "threshold_rejection_proven" not in row:
        return False
    flag = row.get("threshold_rejection_proven", False)
    if not isinstance(flag, bool):
        raise AuditStateError("threshold_rejection_proven must be boolean")
    if not flag:
        return False

    if "threshold_proof_trusted" in row:
        proof_trusted = row["threshold_proof_trusted"]
        if not isinstance(proof_trusted, bool):
            raise AuditStateError("threshold_proof_trusted must be boolean")
        if not proof_trusted:
            raise AuditStateError("threshold proof is explicitly untrusted")
    elif row.get("distance_trusted") is not True:
        raise AuditStateError("legacy threshold proof distance must be trusted")
    n = _strict_int(row.get("n"), "n", minimum=1)
    k = _strict_int(row.get("k"), "k", minimum=1)
    target = _fraction_from_target(row)
    scalar_cutoff, challenge_cutoff = _challenge_cutoff(n, k, target)

    expected_ints = {
        "fom_rejection_cutoff": scalar_cutoff,
        "challenge_rejection_cutoff": challenge_cutoff,
        "minimum_passing_distance": challenge_cutoff + 1,
        "milp_effective_early_stop": challenge_cutoff,
    }
    for name, expected in expected_ints.items():
        observed = _strict_int(row.get(name), name, minimum=0)
        if observed != expected:
            raise AuditStateError(f"{name} does not match the recomputed cutoff")

    if row.get("milp_early_stop_objective") != "challenge_final_gate":
        raise AuditStateError("threshold proof has an unexpected objective")
    if row.get("final_gate_excluded_by_upper_bound") is not True:
        raise AuditStateError("threshold proof does not exclude the final gate")
    if row.get("fom_target_excluded_by_upper_bound") is not True:
        raise AuditStateError("threshold proof does not exclude the FOM target")

    distance = _strict_int(
        row.get("threshold_proof_distance"),
        "threshold_proof_distance",
        minimum=1,
    )
    lhs = _strict_int(row.get("threshold_proof_lhs"), "threshold_proof_lhs")
    rhs = _strict_int(row.get("threshold_proof_rhs"), "threshold_proof_rhs")
    expected_lhs = k * distance * distance * target.denominator
    expected_rhs = target.numerator * n
    if lhs != expected_lhs or rhs != expected_rhs:
        raise AuditStateError("threshold proof integer inequality was not replayed")
    if lhs > rhs or distance > challenge_cutoff:
        raise AuditStateError("threshold proof upper bound does not reject the gate")

    source = row.get("threshold_proof_source")
    if source == "milp_exact":
        if _strict_int(row.get("d"), "d", minimum=1) != distance:
            raise AuditStateError(
                "milp_exact threshold distance disagrees with exact distance"
            )
        details = row.get("milp_details")
        if not isinstance(details, Mapping):
            raise AuditStateError("milp_exact threshold requires milp_details")
        _positive_direction_distance(details, distance)
        _replay_embedded_direction_witness(row, details, distance)
    elif source == "milp_feasible_upper_bound":
        if row.get("milp_solver_attempted") is not True:
            raise AuditStateError(
                "MILP feasible threshold source was not solver-derived"
            )
        details = row.get("milp_details")
        if not isinstance(details, Mapping):
            raise AuditStateError(
                "MILP feasible threshold source requires milp_details"
            )
        if _optional_bool(details, "all_timeout") or _optional_bool(
            details, "no_incumbent"
        ):
            raise AuditStateError(
                "MILP feasible threshold source has no incumbent"
            )
        if row.get("distance_status") in {
            "unknown",
            "unknown_no_incumbent",
            "hard_timeout",
        }:
            raise AuditStateError(
                "MILP feasible threshold source has unknown distance"
            )
        details_exact = details.get("exact", False)
        if not isinstance(details_exact, bool):
            raise AuditStateError("milp_details.exact must be boolean")
        if details_exact:
            raise AuditStateError(
                "fully exact MILP proof must use milp_exact source"
            )
        incumbents = _strict_int(
            details.get("logicals_incumbent"),
            "milp_details.logicals_incumbent",
            minimum=0,
        )
        optimal = _strict_int(
            details.get("logicals_optimal"),
            "milp_details.logicals_optimal",
            minimum=0,
        )
        checked = _strict_int(
            details.get("num_logicals_checked"),
            "milp_details.num_logicals_checked",
            minimum=0,
        )
        if incumbents + optimal < 1 or checked < incumbents + optimal:
            raise AuditStateError(
                "MILP feasible threshold source has no incumbent/optimal evidence"
            )
        _positive_direction_distance(details, distance)
        _replay_embedded_direction_witness(row, details, distance)
    elif source == "symplectic_upper_bound":
        symplectic = _strict_int(
            row.get("d_symplectic"), "d_symplectic", minimum=1
        )
        if symplectic != distance:
            raise AuditStateError(
                "symplectic threshold distance disagrees with its witness"
            )
        witness = row.get("threshold_proof_witness")
        if not isinstance(witness, Mapping):
            raise AuditStateError(
                "symplectic threshold proof witness is missing"
            )
        if row.get("symplectic_weight_witness") != dict(witness):
            raise AuditStateError(
                "symplectic threshold proof witness is inconsistent"
            )
    else:
        raise AuditStateError("threshold proof source is not a trusted upper bound")
    return True


def classify_evaluation(
    row: Mapping[str, Any],
    *,
    fully_exact: FullyExact | None = None,
) -> AuditOutcome:
    """Classify one evaluation without trusting reviewer or raw FOM claims."""
    if not isinstance(row, Mapping):
        raise AuditStateError("evaluation row must be an object")

    if fully_exact is None:
        claimed_exact = is_fully_exact(row)
    else:
        claimed_exact = fully_exact(row)
        if not isinstance(claimed_exact, bool):
            raise AuditStateError("fully_exact callback must return a boolean")
    attempt = _audit_attempt(row)
    try:
        formal_validation = _validated_formal_checkpoint(
            row,
            attempt,
            verify_exact=claimed_exact,
        )
    except AuditEvidenceImplementationMismatch:
        # Source upgrades invalidate old lower-bound attestations but do not
        # prove the candidate bad. Keep it in the retry lane; the candidate-
        # bound working checkpoint is separately archived and recomputed.
        formal_validation = None
    exact = bool(
        claimed_exact
        and formal_validation is not None
        and formal_validation.exact_replay_verified
    )
    formal_checkpoint = (
        formal_validation.checkpoint
        if formal_validation is not None
        else None
    )
    threshold_rejected = _verified_threshold_rejection(
        row,
        fully_exact=exact,
        formal_checkpoint=formal_checkpoint,
    )

    if exact and formal_checkpoint is not None:
        return AuditOutcome.EXACT
    if threshold_rejected:
        return AuditOutcome.THRESHOLD_REJECTED

    details = row.get("milp_details", {})
    if details is None:
        details = {}
    if not isinstance(details, Mapping):
        raise AuditStateError("milp_details must be an object")
    no_incumbent = any(
        (
            _optional_bool(details, "all_timeout"),
            _optional_bool(details, "no_incumbent"),
            row.get("distance_status")
            in {"unknown", "unknown_no_incumbent", "hard_timeout"},
            row.get("stage") == "milp_timeout_no_incumbent",
        )
    )
    if no_incumbent:
        return AuditOutcome.UNRESOLVED_NO_INCUMBENT
    return AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED


def _normalise_terms(value: Any, label: str) -> list[list[int]]:
    if not isinstance(value, list) or not value:
        raise AuditStateError(f"{label} must be a non-empty list")
    terms: list[list[int]] = []
    for index, term in enumerate(value):
        if not isinstance(term, (list, tuple)) or len(term) != 2:
            raise AuditStateError(f"{label}[{index}] must contain two integers")
        terms.append(
            [
                _strict_int(term[0], f"{label}[{index}][0]"),
                _strict_int(term[1], f"{label}[{index}][1]"),
            ]
        )
    return sorted(terms)


@lru_cache(maxsize=4096)
def _canonical_css_digest_for_definition(
    ell: int,
    m: int,
    a_terms: tuple[tuple[int, int], ...],
    b_terms: tuple[tuple[int, int], ...],
    geometry_json: str,
) -> str:
    """Rebuild one CSS BB code and return its authoritative Tanner digest."""
    from evaluation.bb_code import build_bb_code
    from evaluation.structural_dedup import canonical_digest

    geometry = json.loads(geometry_json)
    code = build_bb_code(
        ell, m, list(a_terms), list(b_terms), geometry=geometry,
    )
    digest = canonical_digest(code)
    if (
        not isinstance(digest, str)
        or len(digest) != 64
        or any(character not in "0123456789abcdef" for character in digest)
    ):
        raise ValueError("canonical digest implementation returned invalid data")
    return digest


def _verified_structural_digest(
    *,
    ell: int,
    m: int,
    a_terms: list[list[int]],
    b_terms: list[list[int]],
    geometry: Mapping[str, Any] | None,
    reported_digest: Any,
) -> str | None:
    """Return only a digest independently derived from the candidate.

    The reported value is never an identity authority, including for legacy
    rows where it is absent.  Always rebuild the code and canonicalize its
    colored Tanner graph; a matching report is merely retained verbatim.
    Failure to perform that independent computation is fail-closed rather than
    silently trusting attacker-controlled, stale, or missing metadata.
    """
    if reported_digest is not None and (
        not isinstance(reported_digest, str) or not reported_digest
    ):
        raise AuditStateError("canonical_digest must be a non-empty string")
    try:
        recomputed = _canonical_css_digest_for_definition(
            ell,
            m,
            tuple(tuple(term) for term in a_terms),
            tuple(tuple(term) for term in b_terms),
            json.dumps(
                geometry,
                sort_keys=True,
                separators=(",", ":"),
            ),
        )
    except Exception as exc:
        raise AuditStateError(
            "canonical_digest could not be independently recomputed"
        ) from exc
    if reported_digest is None:
        return recomputed
    if reported_digest == recomputed:
        return reported_digest
    # A stale or forged report is not fatal because the candidate definition
    # is still available.  Replace it with the independently derived identity
    # so this row cannot hide another candidate by choosing its digest.
    return recomputed


def authoritative_candidate_digest(row: Mapping[str, Any]) -> str:
    """Return a definition-derived Tanner digest, ignoring report authority.

    ``structural_novelty.canonical_digest`` may be absent on legacy rows or may
    be stale/forged.  It is type-checked when present but never controls the
    returned identity.
    """
    ell = _strict_int(row.get("ell"), "ell", minimum=1)
    m = _strict_int(row.get("m"), "m", minimum=1)
    a_terms = _normalise_terms(row.get("A_terms"), "A_terms")
    b_terms = _normalise_terms(row.get("B_terms"), "B_terms")
    geometry = candidate_geometry(row)
    novelty = row.get("structural_novelty")
    if novelty is not None and not isinstance(novelty, Mapping):
        raise AuditStateError("structural_novelty must be an object")
    reported = novelty.get("canonical_digest") if novelty else None
    digest = _verified_structural_digest(
        ell=ell,
        m=m,
        a_terms=a_terms,
        b_terms=b_terms,
        geometry=geometry,
        reported_digest=reported,
    )
    if digest is None:
        # _verified_structural_digest always recomputes; keep this guard so a
        # future implementation cannot silently disable structural identity.
        raise AuditStateError("canonical_digest recomputation returned no digest")
    return digest


def _candidate_snapshot(row: Mapping[str, Any]) -> tuple[str, str | None, dict[str, Any]]:
    ell = _strict_int(row.get("ell"), "ell", minimum=1)
    m = _strict_int(row.get("m"), "m", minimum=1)
    a_terms = _normalise_terms(row.get("A_terms"), "A_terms")
    b_terms = _normalise_terms(row.get("B_terms"), "B_terms")
    geometry = candidate_geometry(row)
    defining = {
        "ell": ell,
        "m": m,
        "A_terms": a_terms,
        "B_terms": b_terms,
    }
    if geometry is not None:
        defining["geometry"] = geometry
    key = code_key(defining)
    reported_key = row.get("candidate_key")
    if reported_key is not None and reported_key != key:
        raise AuditStateError("candidate_key does not match the candidate definition")

    digest = authoritative_candidate_digest(defining | {
        "structural_novelty": row.get("structural_novelty"),
    })

    snapshot_fields = (
        "n",
        "k",
        "d",
        "fom",
        "score",
        "pattern_type",
        "term_count",
        "archive_cell",
        "static_eligibility",
        "structural_novelty",
    )
    snapshot = dict(defining)
    for name in snapshot_fields:
        if name in row:
            snapshot[name] = copy.deepcopy(row[name])
    if digest is not None:
        # Persist the independently recomputed value in retry state.  This
        # makes a stale report self-healing and prevents a later validation
        # from seeing two conflicting identities for the same definition.
        snapshot_novelty = snapshot.get("structural_novelty")
        if snapshot_novelty is None:
            snapshot_novelty = {}
            snapshot["structural_novelty"] = snapshot_novelty
        if not isinstance(snapshot_novelty, dict):
            raise AuditStateError("structural_novelty must be an object")
        snapshot_novelty["canonical_digest"] = digest
    _canonical_json(snapshot, "candidate snapshot")
    snapshot["candidate_key"] = key
    return key, digest, snapshot


def _checkpoint_path(value: str | Path | None) -> str | None:
    if value is None:
        return None
    path = str(value)
    if not path:
        raise AuditStateError("checkpoint_path must not be empty")
    return path


def _audit_attempt(row: Mapping[str, Any]) -> AuditAttempt | None:
    raw = row.get("audit_attempt")
    if raw is None:
        return None
    if not isinstance(raw, Mapping):
        raise AuditStateError("audit_attempt must be an object")
    legacy_fields = {
        "schema_version",
        "round",
        "kind",
        "attempt",
        "multiplier",
        "soft",
        "total",
        "hard",
        "checkpoint",
    }
    schema = _strict_int(
        raw.get("schema_version"),
        "audit_attempt.schema_version",
        minimum=1,
    )
    required = set(legacy_fields)
    if schema == AUDIT_ATTEMPT_VERSION:
        required.update({"candidate_key", "n", "k", "evidence"})
    elif schema != LEGACY_AUDIT_ATTEMPT_VERSION:
        raise AuditStateError("unsupported audit_attempt schema_version")
    observed_fields = set(raw)
    if observed_fields != required:
        missing = sorted(required - observed_fields)
        extra = sorted(observed_fields - required)
        raise AuditStateError(
            "audit_attempt fields are invalid: "
            f"missing={missing}, extra={extra}"
        )
    round_number = _strict_int(
        raw.get("round"), "audit_attempt.round", minimum=1
    )
    attempt = _strict_int(
        raw.get("attempt"), "audit_attempt.attempt", minimum=1
    )
    kind = raw.get("kind")
    expected_kind = "new" if attempt == 1 else "retry"
    if kind != expected_kind:
        raise AuditStateError(
            f"audit_attempt.kind must be {expected_kind!r} for attempt {attempt}"
        )
    multiplier = _validate_multiplier(
        raw.get("multiplier"), "audit_attempt.multiplier"
    )
    expected_multiplier = min(
        1 << min(attempt - 1, 2), MAX_RETRY_MULTIPLIER
    )
    if multiplier != expected_multiplier:
        raise AuditStateError(
            "audit_attempt.multiplier does not match its attempt number"
        )
    soft = _strict_int(raw.get("soft"), "audit_attempt.soft", minimum=1)
    total = _strict_int(raw.get("total"), "audit_attempt.total", minimum=1)
    hard_value = raw.get("hard")
    if (
        isinstance(hard_value, bool)
        or not isinstance(hard_value, (int, float))
        or not math.isfinite(float(hard_value))
        or float(hard_value) <= 0
    ):
        raise AuditStateError(
            "audit_attempt.hard must be a positive finite number"
        )
    checkpoint = _checkpoint_path(raw.get("checkpoint"))
    assert checkpoint is not None
    checkpoint_object = Path(checkpoint)
    if not checkpoint_object.is_absolute() or ".." in checkpoint_object.parts:
        raise AuditStateError(
            "audit_attempt.checkpoint must be an absolute normalized path"
        )
    candidate_key: str | None = None
    n: int | None = None
    k: int | None = None
    evidence: dict[str, Any] | None = None
    if schema == AUDIT_ATTEMPT_VERSION:
        candidate_key = raw.get("candidate_key")
        if (
            not isinstance(candidate_key, str)
            or len(candidate_key) != 20
            or any(character not in "0123456789abcdef" for character in candidate_key)
        ):
            raise AuditStateError("audit_attempt.candidate_key is invalid")
        n = _strict_int(raw.get("n"), "audit_attempt.n", minimum=1)
        k = _strict_int(raw.get("k"), "audit_attempt.k", minimum=1)
        raw_evidence = raw.get("evidence")
        if not isinstance(raw_evidence, Mapping):
            raise AuditStateError("audit_attempt.evidence must be an object")
        if set(raw_evidence) != _EVIDENCE_FIELDS:
            raise AuditStateError("audit_attempt.evidence fields are invalid")
        evidence = copy.deepcopy(dict(raw_evidence))
    return AuditAttempt(
        schema_version=schema,
        round_number=round_number,
        kind=kind,
        attempt=attempt,
        multiplier=multiplier,
        timeout_per_logical=soft,
        total_timeout=total,
        hard_timeout_per_logical=float(hard_value),
        checkpoint_path=checkpoint,
        candidate_key=candidate_key,
        n=n,
        k=k,
        evidence=evidence,
    )


def _result_summary(row: Mapping[str, Any], outcome: AuditOutcome) -> dict[str, Any]:
    summary = {
        "outcome": outcome.value,
        "stage": row.get("stage"),
        "d": row.get("d"),
        "fom": row.get("fom"),
        "distance_status": row.get("distance_status"),
        "d_is_exact": row.get("d_is_exact") is True,
        "threshold_rejection_proven": (
            row.get("threshold_rejection_proven") is True
        ),
        "sha256": hashlib.sha256(
            _canonical_json(row, "evaluation row")
        ).hexdigest(),
    }
    return summary


def _validate_multiplier(value: Any, label: str = "budget_multiplier") -> int:
    multiplier = _strict_int(value, label, minimum=1)
    if multiplier not in {1, 2, MAX_RETRY_MULTIPLIER}:
        raise AuditStateError(f"{label} must be one of 1x, 2x, or 4x")
    return multiplier


def create_unresolved_entry(
    row: Mapping[str, Any],
    *,
    round_number: int,
    budget_multiplier: int = 1,
    attempt_number: int = 1,
    checkpoint_path: str | Path | None = None,
    fully_exact: FullyExact | None = None,
) -> dict[str, Any]:
    """Create a JSON-serializable queue entry from one unresolved result."""
    outcome = classify_evaluation(row, fully_exact=fully_exact)
    if outcome.terminal:
        raise AuditStateError("terminal evaluations cannot enter the unresolved queue")
    round_number = _strict_int(round_number, "round_number", minimum=0)
    multiplier = _validate_multiplier(budget_multiplier)
    attempt_number = _strict_int(
        attempt_number, "attempt_number", minimum=1
    )
    expected_multiplier = min(
        1 << min(attempt_number - 1, 2), MAX_RETRY_MULTIPLIER
    )
    if multiplier != expected_multiplier:
        raise AuditStateError(
            "budget_multiplier does not match attempt_number"
        )
    key, digest, candidate = _candidate_snapshot(row)
    return {
        "schema_version": UNRESOLVED_ENTRY_VERSION,
        "status": "unresolved",
        "candidate_key": key,
        "canonical_digest": digest,
        "candidate": candidate,
        "reason": outcome.value,
        "attempts_started": attempt_number,
        "attempts_completed": attempt_number,
        "first_seen_round": round_number,
        "last_attempt_round": round_number,
        "last_budget_multiplier": multiplier,
        "next_budget_multiplier": min(
            multiplier * 2, MAX_RETRY_MULTIPLIER
        ),
        "checkpoint_path": _checkpoint_path(checkpoint_path),
        "last_result": _result_summary(row, outcome),
    }


def _validate_unresolved_entry(entry: Mapping[str, Any]) -> None:
    if not isinstance(entry, Mapping):
        raise AuditStateError("unresolved entry must be an object")
    if entry.get("schema_version") != UNRESOLVED_ENTRY_VERSION:
        raise AuditStateError("unsupported unresolved entry schema")
    if entry.get("status") != "unresolved":
        raise AuditStateError("unresolved entry has a non-unresolved status")
    candidate = entry.get("candidate")
    if not isinstance(candidate, Mapping):
        raise AuditStateError("unresolved entry candidate must be an object")
    key, digest, _snapshot = _candidate_snapshot(candidate)
    if entry.get("candidate_key") != key:
        raise AuditStateError("unresolved entry candidate_key is inconsistent")
    if entry.get("canonical_digest") != digest:
        raise AuditStateError("unresolved entry canonical_digest is inconsistent")
    reason = entry.get("reason")
    if reason not in {
        AuditOutcome.UNRESOLVED_NO_INCUMBENT.value,
        AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED.value,
    }:
        raise AuditStateError("unresolved entry reason is invalid")
    started = _strict_int(
        entry.get("attempts_started"), "attempts_started", minimum=1
    )
    completed = _strict_int(
        entry.get("attempts_completed"), "attempts_completed", minimum=1
    )
    if started != completed:
        raise AuditStateError("completed unresolved entry has an active attempt")
    _strict_int(entry.get("first_seen_round"), "first_seen_round", minimum=0)
    _strict_int(entry.get("last_attempt_round"), "last_attempt_round", minimum=0)
    last = _validate_multiplier(
        entry.get("last_budget_multiplier"), "last_budget_multiplier"
    )
    following = _validate_multiplier(
        entry.get("next_budget_multiplier"), "next_budget_multiplier"
    )
    if following != min(last * 2, MAX_RETRY_MULTIPLIER):
        raise AuditStateError("next retry budget must grow to and cap at 4x")
    _checkpoint_path(entry.get("checkpoint_path"))
    if not isinstance(entry.get("last_result"), Mapping):
        raise AuditStateError("unresolved entry last_result must be an object")


def update_unresolved_entry(
    entry: Mapping[str, Any],
    row: Mapping[str, Any],
    *,
    round_number: int,
    budget_multiplier: int,
    checkpoint_path: str | Path | None = None,
    fully_exact: FullyExact | None = None,
) -> dict[str, Any]:
    """Record a completed retry that remains unresolved."""
    _validate_unresolved_entry(entry)
    outcome = classify_evaluation(row, fully_exact=fully_exact)
    if outcome.terminal:
        raise AuditStateError("terminal retry must be removed from the queue")
    key, digest, candidate = _candidate_snapshot(row)
    if key != entry["candidate_key"] or digest != entry["canonical_digest"]:
        raise AuditStateError("retry result does not match the queued candidate")
    round_number = _strict_int(round_number, "round_number", minimum=0)
    if round_number < entry["last_attempt_round"]:
        raise AuditStateError("retry round cannot move backwards")
    multiplier = _validate_multiplier(budget_multiplier)
    if multiplier != entry["next_budget_multiplier"]:
        raise AuditStateError("retry budget does not match next_budget_multiplier")

    old_path = _checkpoint_path(entry.get("checkpoint_path"))
    new_path = _checkpoint_path(checkpoint_path)
    if old_path is not None and new_path is not None and old_path != new_path:
        raise AuditStateError("checkpoint_path cannot change across retries")

    updated = copy.deepcopy(dict(entry))
    updated.update(
        {
            "candidate": candidate,
            "reason": outcome.value,
            "attempts_started": entry["attempts_started"] + 1,
            "attempts_completed": entry["attempts_completed"] + 1,
            "last_attempt_round": round_number,
            "last_budget_multiplier": multiplier,
            "next_budget_multiplier": min(
                multiplier * 2, MAX_RETRY_MULTIPLIER
            ),
            "checkpoint_path": old_path or new_path,
            "last_result": _result_summary(row, outcome),
        }
    )
    return updated


def retry_budget(
    *,
    timeout_per_logical: int,
    total_timeout: int,
    completed_attempts: int,
    hard_timeout_per_logical: float | None = None,
) -> RetryBudget:
    """Return base, 2x, 4x, ... budgets from completed-attempt count."""
    per_logical = _strict_int(
        timeout_per_logical, "timeout_per_logical", minimum=0
    )
    total = _strict_int(total_timeout, "total_timeout", minimum=0)
    attempts = _strict_int(completed_attempts, "completed_attempts", minimum=0)
    multiplier = min(1 << min(attempts, 2), MAX_RETRY_MULTIPLIER)

    hard: float | None
    if hard_timeout_per_logical is None:
        hard = None
    else:
        if (
            isinstance(hard_timeout_per_logical, bool)
            or not isinstance(hard_timeout_per_logical, (int, float))
            or not math.isfinite(float(hard_timeout_per_logical))
            or hard_timeout_per_logical <= 0
        ):
            raise AuditStateError(
                "hard_timeout_per_logical must be a positive finite number"
            )
        if per_logical > 0 and hard_timeout_per_logical < per_logical:
            raise AuditStateError(
                "hard_timeout_per_logical cannot be below the soft timeout"
            )
        hard = float(hard_timeout_per_logical) * multiplier

    return RetryBudget(
        multiplier=multiplier,
        timeout_per_logical=per_logical * multiplier,
        total_timeout=total * multiplier,
        hard_timeout_per_logical=hard,
    )


def select_retry_lane(
    unresolved: Mapping[str, Mapping[str, Any]],
    *,
    limit: int = 1,
) -> list[dict[str, Any]]:
    """Select least-recently-attempted entries with deterministic tie breaks."""
    if not isinstance(unresolved, Mapping):
        raise AuditStateError("unresolved queue must be an object")
    limit = _strict_int(limit, "limit", minimum=0)
    validated: list[dict[str, Any]] = []
    for key, raw in unresolved.items():
        if not isinstance(key, str) or not key:
            raise AuditStateError("unresolved queue keys must be non-empty strings")
        _validate_unresolved_entry(raw)
        if raw["candidate_key"] != key:
            raise AuditStateError("unresolved queue key does not match candidate_key")
        validated.append(copy.deepcopy(dict(raw)))
    validated.sort(
        key=lambda item: (
            item["last_attempt_round"],
            item["attempts_completed"],
            item["first_seen_round"],
            item["candidate_key"],
        )
    )
    return validated[:limit]


def _legacy_audit_round(row: Mapping[str, Any]) -> int | None:
    if "audit_round" in row:
        return _strict_int(row["audit_round"], "audit_round", minimum=1)
    return None


def _row_checkpoint(
    row: Mapping[str, Any],
    key: str,
    checkpoint_path_for: CheckpointPathFor | None,
    *,
    attempt: AuditAttempt | None = None,
) -> str | None:
    details = row.get("milp_details")
    if details is not None and not isinstance(details, Mapping):
        raise AuditStateError("milp_details must be an object")
    recorded = details.get("checkpoint_path") if details else None
    attempted = attempt.checkpoint_path if attempt is not None else None
    generated = checkpoint_path_for(key) if checkpoint_path_for else None
    recorded_path = _checkpoint_path(recorded)
    attempted_path = _checkpoint_path(attempted)
    generated_path = _checkpoint_path(generated)
    observed = [
        path
        for path in (recorded_path, attempted_path, generated_path)
        if path is not None
    ]
    if len(set(observed)) > 1:
        raise AuditStateError("recorded checkpoint path disagrees with policy")
    return attempted_path or recorded_path or generated_path

def rebuild_audit_state(
    rows: Iterable[Mapping[str, Any]],
    *,
    fully_exact: FullyExact | None = None,
    checkpoint_path_for: CheckpointPathFor | None = None,
) -> RebuiltAuditState:
    """Rebuild retry state using only definition-derived structural digests."""
    terminal_keys: set[str] = set()
    terminal_digests: set[str] = set()
    unresolved: dict[str, dict[str, Any]] = {}
    digests_by_key: dict[str, str | None] = {}
    attempts_by_key: dict[str, int] = {}
    last_ordered_round_by_key: dict[str, int] = {}
    explicit_started_by_key: set[str] = set()
    checkpoints_by_key: dict[str, str | None] = {}
    budget_bases_by_key: dict[str, tuple[int, int, float]] = {}
    count = 0

    for index, row in enumerate(rows):
        count += 1
        try:
            if not isinstance(row, Mapping):
                raise AuditStateError("evaluation row must be an object")
            key, digest, _candidate = _candidate_snapshot(row)
            previous_digest = digests_by_key.setdefault(key, digest)
            if previous_digest != digest:
                raise AuditStateError(
                    "canonical_digest changed across one candidate's history"
                )

            attempt = _audit_attempt(row)
            previous_attempts = attempts_by_key.get(key, 0)
            if attempt is None:
                if key in explicit_started_by_key:
                    raise AuditStateError(
                        "legacy evaluation cannot follow an explicit audit_attempt"
                    )
                attempt_number = previous_attempts + 1
                multiplier = min(
                    1 << min(attempt_number - 1, 2),
                    MAX_RETRY_MULTIPLIER,
                )
                legacy_round = _legacy_audit_round(row)
                if legacy_round is None:
                    if key in last_ordered_round_by_key:
                        raise AuditStateError(
                            "legacy unknown epoch cannot follow an ordered audit_round"
                        )
                    round_number = 0
                else:
                    previous_round = last_ordered_round_by_key.get(key, 0)
                    if legacy_round <= previous_round:
                        raise AuditStateError(
                            "legacy audit_round values must strictly increase"
                        )
                    round_number = legacy_round
                    last_ordered_round_by_key[key] = round_number
            else:
                attempt_number = attempt.attempt
                if attempt_number != previous_attempts + 1:
                    raise AuditStateError(
                        "audit_attempt.attempt is not contiguous"
                    )
                multiplier = attempt.multiplier
                round_number = attempt.round_number
                previous_round = last_ordered_round_by_key.get(key, 0)
                if round_number <= previous_round:
                    raise AuditStateError(
                        "explicit audit attempt rounds must strictly increase"
                    )
                explicit_started_by_key.add(key)
                last_ordered_round_by_key[key] = round_number
                if (
                    attempt.timeout_per_logical % multiplier
                    or attempt.total_timeout % multiplier
                ):
                    raise AuditStateError(
                        "audit_attempt budgets are not integer multiplier scales"
                    )
                budget_base = (
                    attempt.timeout_per_logical // multiplier,
                    attempt.total_timeout // multiplier,
                    attempt.hard_timeout_per_logical / multiplier,
                )
                previous_base = budget_bases_by_key.setdefault(key, budget_base)
                if (
                    previous_base[:2] != budget_base[:2]
                    or not math.isclose(
                        previous_base[2],
                        budget_base[2],
                        rel_tol=0.0,
                        abs_tol=1e-9,
                    )
                ):
                    raise AuditStateError(
                        "audit_attempt budgets changed their base policy"
                    )
            checkpoint = _row_checkpoint(
                row,
                key,
                checkpoint_path_for,
                attempt=attempt,
            )
            previous_checkpoint = checkpoints_by_key.setdefault(key, checkpoint)
            if (
                previous_checkpoint is not None
                and checkpoint is not None
                and previous_checkpoint != checkpoint
            ):
                raise AuditStateError(
                    "checkpoint path changed across candidate history"
                )
            if previous_checkpoint is None and checkpoint is not None:
                checkpoints_by_key[key] = checkpoint
            attempts_by_key[key] = attempt_number

            outcome = classify_evaluation(row, fully_exact=fully_exact)
            if outcome.terminal:
                terminal_keys.add(key)
                if digest:
                    terminal_digests.add(digest)
                unresolved.pop(key, None)
                continue
            if key in terminal_keys:
                continue

            current = unresolved.get(key)
            if current is None:
                if attempt_number != 1:
                    raise AuditStateError(
                        "unresolved history starts after its first attempt"
                    )
                unresolved[key] = create_unresolved_entry(
                    row,
                    round_number=round_number,
                    budget_multiplier=multiplier,
                    attempt_number=attempt_number,
                    checkpoint_path=checkpoint,
                    fully_exact=fully_exact,
                )
            else:
                if attempt_number != current["attempts_completed"] + 1:
                    raise AuditStateError(
                        "unresolved attempt count is inconsistent"
                    )
                unresolved[key] = update_unresolved_entry(
                    current,
                    row,
                    round_number=round_number,
                    budget_multiplier=multiplier,
                    checkpoint_path=checkpoint,
                    fully_exact=fully_exact,
                )
        except AuditStateError as exc:
            raise AuditStateError(f"evaluation[{index}]: {exc}") from exc

    collapsed: dict[str, dict[str, Any]] = {}
    unresolved_digest_owners: set[str] = set()
    for key, entry in unresolved.items():
        digest = entry.get("canonical_digest")
        if digest and digest in terminal_digests:
            continue
        if digest and digest in unresolved_digest_owners:
            continue
        collapsed[key] = entry
        if digest:
            unresolved_digest_owners.add(digest)
    return RebuiltAuditState(
        terminal_keys=frozenset(terminal_keys),
        terminal_digests=frozenset(terminal_digests),
        unresolved=collapsed,
        evaluations_seen=count,
    )
