"""Proof-safe low-weight search oracle for CSS codes.

The oracle answers one deliberately narrow question: does either logical
sector contain a non-trivial operator of weight at most ``w``?  Its semantics
are asymmetric and are part of the public contract:

* ``SAT`` carries an operator which is replayed from the supplied matrices and
  is therefore a valid distance upper-bound witness.
* ``UNSAT`` is returned only after *both* X and Z sectors are complete, giving
  the search-only lower bound ``d >= w + 1``.
* ``UNKNOWN`` (timeout, missing backend, malformed solver response) gives no
  mathematical credit and must remain retryable.

Thresholds through four use a deterministic meet-in-the-middle enumeration,
so the hot search path does not depend on the optional python-sat package.
Larger thresholds delegate to :mod:`evaluation.distance_sat`, whose child
process supplies a hard wall timeout and terminal-only checkpoint semantics.
Publication certification still belongs to the later exact pipeline stages;
this module exists to make evolutionary fitness correlate with a real lower
bound and to return concrete failure witnesses for mutation feedback.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import math
import time
from pathlib import Path
from typing import Any, Literal, Mapping

import numpy as np

from evaluation.css_logical_detector import verify_css_logical_detectors
from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_FORMULATION,
    css_sector_matrices,
    solve_css_threshold_sat,
    verify_css_threshold_sat_witness,
)


LOW_WEIGHT_ORACLE_KIND = "qcode-css-low-weight-oracle"
LOW_WEIGHT_ORACLE_SCHEMA_VERSION = 1
LOW_WEIGHT_SECTOR_KIND = "qcode-css-low-weight-sector-evidence"
LOW_WEIGHT_MITM_MAX_THRESHOLD = 4
LOW_WEIGHT_MITM_ENGINE = "css-column-xor-mitm-v1"
LOW_WEIGHT_SAT_ENGINE = "css-global-threshold-sat-v1"
LOW_WEIGHT_OUTCOMES = frozenset({"SAT", "UNSAT", "UNKNOWN"})

try:
    _SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
except OSError:
    _SOURCE_SHA256 = None


def _canonical_json_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode("ascii"))
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _validated_sector_problem(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
) -> tuple[np.ndarray, np.ndarray, int, str]:
    check_matrix = np.asarray(checks, dtype=np.uint8) & 1
    target_logicals = np.asarray(logicals, dtype=np.uint8) & 1
    normalized_sector = str(sector).upper()
    if normalized_sector not in {"X", "Z"}:
        raise ValueError("sector must be X or Z")
    if check_matrix.ndim != 2 or target_logicals.ndim != 2:
        raise ValueError("checks and target_logicals must be matrices")
    if (
        check_matrix.shape[1] < 1
        or target_logicals.shape[0] < 1
        or target_logicals.shape[1] != check_matrix.shape[1]
    ):
        raise ValueError("logical/check matrix dimensions are incompatible")
    if isinstance(max_weight, bool) or not isinstance(
        max_weight, (int, np.integer)
    ):
        raise ValueError("max_weight must be an integer")
    threshold = int(max_weight)
    if threshold < 0:
        raise ValueError("max_weight must be nonnegative")
    return check_matrix, target_logicals, threshold, normalized_sector


def _packed_column_integers(matrix: np.ndarray) -> list[int]:
    """Pack each GF(2) column into a deterministic Python integer."""

    if matrix.shape[0] == 0:
        return [0] * int(matrix.shape[1])
    packed = np.packbits(matrix.T, axis=1, bitorder="little")
    return [int.from_bytes(row.tobytes(), "little") for row in packed]


def _subset_records(
    check_columns: list[int],
    logical_columns: list[int],
    limit: int,
):
    n = len(check_columns)
    for size in range(limit + 1):
        for support in itertools.combinations(range(n), size):
            check_value = 0
            logical_value = 0
            for index in support:
                check_value ^= check_columns[index]
                logical_value ^= logical_columns[index]
            yield check_value, logical_value, support


def _witness_from_support(
    support: tuple[int, ...],
    *,
    checks: np.ndarray,
    logicals: np.ndarray,
    sector: str,
) -> dict[str, Any]:
    vector = np.zeros(checks.shape[1], dtype=np.uint8)
    if support:
        vector[np.asarray(support, dtype=int)] = 1
    syndrome = ((logicals @ vector) & 1).astype(int).tolist()
    if np.any((checks @ vector) & 1) or not any(syndrome):
        raise RuntimeError("low-weight MITM produced an invalid logical witness")
    logical_index = next(index for index, bit in enumerate(syndrome) if bit)
    return {
        "side": sector,
        "index": logical_index,
        "weight": int(vector.sum()),
        "bits": vector.astype(int).tolist(),
        "logical_syndrome": syndrome,
        "support": [int(index) for index in np.flatnonzero(vector)],
    }


def _sector_binding(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    threshold: int,
    sector: str,
    engine: str,
    source_sha256: str | None = None,
) -> dict[str, Any]:
    selected_source = (
        _SOURCE_SHA256 if source_sha256 is None else source_sha256
    )
    if (
        not isinstance(selected_source, str)
        or len(selected_source) != 64
        or any(
            character not in "0123456789abcdef"
            for character in selected_source
        )
    ):
        raise RuntimeError("cannot fingerprint low_weight_oracle.py")
    binding = {
        "source_sha256": selected_source,
        "engine": engine,
        "sector": sector,
        "n": int(checks.shape[1]),
        "num_checks": int(checks.shape[0]),
        "num_logicals": int(logicals.shape[0]),
        "max_weight": threshold,
        "check_matrix_sha256": _array_sha256("checks", checks),
        "target_logicals_sha256": _array_sha256("logicals", logicals),
    }
    binding["binding_sha256"] = _canonical_json_sha256(binding)
    return binding


def _seal_sector_evidence(evidence: dict[str, Any]) -> dict[str, Any]:
    unsigned = dict(evidence)
    unsigned.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = _canonical_json_sha256(unsigned)
    return evidence


def _solve_sector_mitm(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
) -> dict[str, Any]:
    """Exhaust one sector through weight four using XOR meet-in-the-middle."""

    started = time.monotonic()
    threshold = int(max_weight)
    binding = _sector_binding(
        checks,
        logicals,
        threshold=threshold,
        sector=sector,
        engine=LOW_WEIGHT_MITM_ENGINE,
    )
    check_columns = _packed_column_integers(checks)
    logical_columns = _packed_column_integers(logicals)
    left_limit = threshold // 2
    right_limit = threshold - left_limit

    # One support per (check XOR, logical XOR) is sufficient here: every left
    # and right support has size at most its half-limit, so any matched pair's
    # symmetric difference automatically respects the threshold.  Keeping the
    # first representative makes evidence deterministic and memory bounded.
    left: dict[int, dict[int, tuple[int, ...]]] = {}
    enumerated_left = 0
    for check_value, logical_value, support in _subset_records(
        check_columns, logical_columns, left_limit
    ):
        enumerated_left += 1
        left.setdefault(check_value, {}).setdefault(logical_value, support)

    enumerated_right = 0
    witness: dict[str, Any] | None = None
    for check_value, logical_value, support in _subset_records(
        check_columns, logical_columns, right_limit
    ):
        enumerated_right += 1
        matches = left.get(check_value)
        if matches is None:
            continue
        for left_logical, left_support in matches.items():
            if left_logical == logical_value:
                continue
            combined = tuple(sorted(set(left_support).symmetric_difference(support)))
            if not combined or len(combined) > threshold:
                continue
            witness = _witness_from_support(
                combined,
                checks=checks,
                logicals=logicals,
                sector=sector,
            )
            break
        if witness is not None:
            break

    outcome = "SAT" if witness is not None else "UNSAT"
    return _seal_sector_evidence({
        "schema_version": LOW_WEIGHT_ORACLE_SCHEMA_VERSION,
        "kind": LOW_WEIGHT_SECTOR_KIND,
        "outcome": outcome,
        "decision_complete": True,
        "retryable": False,
        "binding": binding,
        "max_weight": threshold,
        "witness": witness,
        "enumeration": {
            "left_limit": left_limit,
            "right_limit": right_limit,
            "left_subsets": enumerated_left,
            "right_subsets": enumerated_right,
        },
        "elapsed_s": time.monotonic() - started,
    })


def _unpack_sat_operator(record: Mapping[str, Any]) -> np.ndarray:
    try:
        length = int(record["length"])
        packed = bytes.fromhex(str(record["packed_hex"]))
        expected_weight = int(record["weight"])
        expected_sha256 = str(record["sha256"])
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("invalid packed SAT operator") from exc
    if length < 1:
        raise ValueError("invalid packed SAT operator length")
    vector = np.unpackbits(
        np.frombuffer(packed, dtype=np.uint8), bitorder="little"
    )[:length].astype(np.uint8)
    actual_sha256 = hashlib.sha256(f"{length}:".encode() + packed).hexdigest()
    if int(vector.sum()) != expected_weight or actual_sha256 != expected_sha256:
        raise ValueError("packed SAT operator metadata mismatch")
    return vector


def _current_distance_sat_source_sha256() -> str | None:
    """Return the exact source digest expected in SAT instance evidence."""

    try:
        from evaluation import distance_sat

        return hashlib.sha256(Path(distance_sat.__file__).read_bytes()).hexdigest()
    except (OSError, TypeError):
        return None


def _sat_backend_terminal_failures(
    evidence: Mapping[str, Any],
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    checkpoint_identity: Mapping[str, Any],
) -> list[str]:
    """Validate all metadata needed to trust a terminal SAT decision.

    A SAT operator is still replayed algebraically by the caller. An UNSAT
    result has no compact proof object, so it is promoted to a search lower
    bound only when the terminal record, current solver source, matrices, and
    caller identity all match exactly.
    """

    failures: list[str] = []
    unsigned = dict(evidence)
    evidence_sha256 = unsigned.pop("evidence_sha256", None)
    try:
        evidence_hash_valid = evidence_sha256 == _canonical_json_sha256(unsigned)
    except (TypeError, ValueError):
        evidence_hash_valid = False
    if not evidence_hash_valid:
        failures.append("SAT backend evidence hash is invalid")

    outcome = evidence.get("outcome")
    expected_infeasible = outcome == "unsat"
    if (
        evidence.get("schema_version") != SAT_EVIDENCE_SCHEMA_VERSION
        or evidence.get("evidence_kind") != SAT_EVIDENCE_KIND
        or evidence.get("formulation") != SAT_FORMULATION
        or outcome not in {"sat", "unsat"}
        or evidence.get("decision_complete") is not True
        or evidence.get("threshold_infeasible") is not expected_infeasible
        or evidence.get("retryable") is not False
        or evidence.get("sector") != sector
        or evidence.get("max_weight") != max_weight
        or evidence.get("partition_index") is not None
        or evidence.get("anchor_indices") != []
        or evidence.get("zero_anchor_indices") != []
        or evidence.get("one_anchor_index") is not None
        or evidence.get("anchor_cube_sha256") is not None
    ):
        failures.append("SAT backend terminal semantics are invalid")

    instance = evidence.get("instance")
    if not isinstance(instance, Mapping):
        failures.append("SAT backend instance binding is missing")
        return failures
    binding = dict(instance)
    binding_sha256 = binding.pop("binding_sha256", None)
    try:
        binding_hash_valid = binding_sha256 == _canonical_json_sha256(binding)
    except (TypeError, ValueError):
        binding_hash_valid = False
    if not binding_hash_valid:
        failures.append("SAT backend instance binding hash is invalid")
    current_sat_source = _current_distance_sat_source_sha256()
    if current_sat_source is None:
        failures.append("current SAT backend source cannot be fingerprinted")
    if not (
        instance.get("formulation") == SAT_FORMULATION
        and instance.get("source_sha256") == current_sat_source
        and instance.get("sector") == sector
        and instance.get("n") == int(checks.shape[1])
        and instance.get("num_checks") == int(checks.shape[0])
        and instance.get("num_logicals") == int(logicals.shape[0])
        and instance.get("check_matrix_sha256")
        == _array_sha256("checks", checks)
        and instance.get("target_logicals_sha256")
        == _array_sha256("logicals", logicals)
        and instance.get("max_weight") == max_weight
        and instance.get("partition_index") is None
        and instance.get("anchor_indices") == []
        and instance.get("checkpoint_identity") == dict(checkpoint_identity)
        and instance.get("backend") == evidence.get("backend")
        and instance.get("cardinality_encoding")
        == evidence.get("cardinality_encoding")
    ):
        failures.append("SAT backend evidence is not bound to this matrix instance")

    if outcome == "unsat" and not (
        evidence.get("success") is False
        and evidence.get("operator") is None
        and evidence.get("objective") is None
        and evidence.get("logical_syndrome") is None
    ):
        failures.append("SAT backend UNSAT carries inconsistent witness metadata")
    return failures


def _solve_sector_sat(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    hard_timeout_s: float,
) -> dict[str, Any]:
    started = time.monotonic()
    binding = _sector_binding(
        checks,
        logicals,
        threshold=max_weight,
        sector=sector,
        engine=LOW_WEIGHT_SAT_ENGINE,
    )
    checkpoint_identity = {
        "kind": LOW_WEIGHT_ORACLE_KIND,
        "binding_sha256": binding["binding_sha256"],
    }
    raw = solve_css_threshold_sat(
        checks,
        logicals,
        max_weight=max_weight,
        sector=sector,
        hard_timeout_s=hard_timeout_s,
        checkpoint_identity=checkpoint_identity,
    )
    raw_outcome = raw.get("outcome")
    witness = None
    terminal_failures = (
        _sat_backend_terminal_failures(
            raw,
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
            checkpoint_identity=checkpoint_identity,
        )
        if raw_outcome in {"sat", "unsat"}
        else []
    )
    if terminal_failures:
        outcome = "UNKNOWN"
        message = "SAT terminal evidence rejected: " + "; ".join(
            terminal_failures
        )
    elif raw_outcome == "sat":
        failures = verify_css_threshold_sat_witness(raw, checks, logicals)
        if failures:
            outcome = "UNKNOWN"
            message = "SAT witness replay failed: " + "; ".join(failures)
        else:
            try:
                vector = _unpack_sat_operator(raw["operator"])
            except (KeyError, TypeError, ValueError) as exc:
                outcome = "UNKNOWN"
                message = f"SAT witness unpack failed: {exc}"
            else:
                syndrome = ((logicals @ vector) & 1).astype(int).tolist()
                index = next(i for i, bit in enumerate(syndrome) if bit)
                witness = {
                    "side": sector,
                    "index": index,
                    "weight": int(vector.sum()),
                    "bits": vector.astype(int).tolist(),
                    "logical_syndrome": syndrome,
                    "support": [int(i) for i in np.flatnonzero(vector)],
                }
                outcome = "SAT"
                message = None
    elif raw_outcome == "unsat":
        outcome = "UNSAT"
        message = None
    else:
        outcome = "UNKNOWN"
        message = str(raw.get("message", raw_outcome or "unknown SAT outcome"))
    return _seal_sector_evidence({
        "schema_version": LOW_WEIGHT_ORACLE_SCHEMA_VERSION,
        "kind": LOW_WEIGHT_SECTOR_KIND,
        "outcome": outcome,
        "decision_complete": outcome in {"SAT", "UNSAT"},
        "retryable": outcome == "UNKNOWN",
        "binding": binding,
        "max_weight": int(max_weight),
        "witness": witness,
        "solver_evidence": raw,
        "message": message,
        "elapsed_s": time.monotonic() - started,
    })


def _solve_sector(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    hard_timeout_s: float,
) -> dict[str, Any]:
    if max_weight <= LOW_WEIGHT_MITM_MAX_THRESHOLD:
        return _solve_sector_mitm(
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
        )
    return _solve_sector_sat(
        checks,
        logicals,
        max_weight=max_weight,
        sector=sector,
        hard_timeout_s=hard_timeout_s,
    )


def evaluate_low_weight_sector(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    hard_timeout_s: float = 30.0,
) -> dict[str, Any]:
    """Solve one source-bound low-weight sector problem.

    This is the reusable primitive behind the full CSS oracle.  In
    particular, callers may restrict the columns to a proven coordinate
    subset (for example one block of a two-block construction).  An UNSAT
    result then applies *only* to that restricted problem; callers must not
    promote it to a lower bound on the unrestricted CSS distance.
    """

    check_matrix, target_logicals, threshold, normalized_sector = (
        _validated_sector_problem(
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
        )
    )
    timeout = float(hard_timeout_s)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("hard_timeout_s must be positive and finite")
    return _solve_sector(
        check_matrix,
        target_logicals,
        max_weight=threshold,
        sector=normalized_sector,
        hard_timeout_s=timeout,
    )


def verify_low_weight_sector_evidence(
    evidence: Mapping[str, Any],
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
    require_current_source: bool = True,
    replay_mitm_unsat: bool = True,
) -> list[str]:
    """Replay a standalone sector decision against the exact matrices.

    Historical-source relaxation is deliberately limited to SAT witnesses,
    whose algebraic content is independently replayed.  Search-only UNSAT
    decisions remain tied to the current implementation and SAT backend.
    """

    if type(require_current_source) is not bool:
        raise TypeError("require_current_source must be a boolean")
    if type(replay_mitm_unsat) is not bool:
        raise TypeError("replay_mitm_unsat must be a boolean")
    try:
        check_matrix, target_logicals, threshold, normalized_sector = (
            _validated_sector_problem(
                checks,
                logicals,
                max_weight=max_weight,
                sector=sector,
            )
        )
    except (TypeError, ValueError) as exc:
        return [f"sector matrices are invalid: {exc}"]
    if not isinstance(evidence, Mapping):
        return ["sector evidence is not an object"]

    failures: list[str] = []
    unsigned = dict(evidence)
    evidence_sha256 = unsigned.pop("evidence_sha256", None)
    try:
        if evidence_sha256 != _canonical_json_sha256(unsigned):
            failures.append("sector evidence self-hash mismatch")
    except (TypeError, ValueError):
        failures.append("sector evidence is not strict JSON")

    outcome = evidence.get("outcome")
    expected_complete = outcome in {"SAT", "UNSAT"}
    if not (
        evidence.get("schema_version") == LOW_WEIGHT_ORACLE_SCHEMA_VERSION
        and evidence.get("kind") == LOW_WEIGHT_SECTOR_KIND
        and outcome in LOW_WEIGHT_OUTCOMES
        and evidence.get("max_weight") == threshold
        and evidence.get("decision_complete") is expected_complete
        and evidence.get("retryable") is (not expected_complete)
    ):
        failures.append("sector schema or terminal/retry semantics are invalid")
        if outcome not in LOW_WEIGHT_OUTCOMES:
            return failures

    binding = evidence.get("binding")
    engine = binding.get("engine") if isinstance(binding, Mapping) else None
    if engine not in {LOW_WEIGHT_MITM_ENGINE, LOW_WEIGHT_SAT_ENGINE}:
        failures.append("sector engine/binding is invalid")
        return failures
    declared_source = binding.get("source_sha256")
    declared_source_valid = bool(
        isinstance(declared_source, str)
        and len(declared_source) == 64
        and not any(
            character not in "0123456789abcdef"
            for character in declared_source
        )
    )
    if not declared_source_valid:
        failures.append("sector source binding is invalid")
    elif require_current_source and declared_source != _SOURCE_SHA256:
        failures.append("sector source binding mismatch")
    if not require_current_source and outcome != "SAT":
        failures.append(
            "historical-source relaxation is restricted to SAT upper-bound "
            "witnesses"
        )
    expected_binding = _sector_binding(
        check_matrix,
        target_logicals,
        threshold=threshold,
        sector=normalized_sector,
        engine=str(engine),
        source_sha256=(
            None
            if require_current_source or not declared_source_valid
            else str(declared_source)
        ),
    )
    if not isinstance(binding, Mapping) or dict(binding) != expected_binding:
        failures.append("sector matrix/source binding mismatch")
    if engine == LOW_WEIGHT_MITM_ENGINE and threshold > LOW_WEIGHT_MITM_MAX_THRESHOLD:
        failures.append("sector MITM threshold exceeds its complete range")
    if engine == LOW_WEIGHT_SAT_ENGINE and threshold <= LOW_WEIGHT_MITM_MAX_THRESHOLD:
        failures.append("sector SAT engine used inside the MITM range")

    if outcome == "SAT":
        failures.extend(
            _verify_normalized_witness(
                evidence.get("witness"),
                checks=check_matrix,
                logicals=target_logicals,
                sector=normalized_sector,
                threshold=threshold,
            )
        )
    elif evidence.get("witness") is not None:
        failures.append("non-SAT sector evidence carries a witness")

    if (
        replay_mitm_unsat
        and engine == LOW_WEIGHT_MITM_ENGINE
        and outcome == "UNSAT"
    ):
        replay = _solve_sector_mitm(
            check_matrix,
            target_logicals,
            max_weight=threshold,
            sector=normalized_sector,
        )
        if replay.get("outcome") != "UNSAT":
            failures.append("sector MITM UNSAT does not replay")
    elif engine == LOW_WEIGHT_SAT_ENGINE and outcome in {"SAT", "UNSAT"}:
        raw = evidence.get("solver_evidence")
        if not isinstance(raw, Mapping):
            failures.append("sector SAT terminal evidence is missing")
        elif isinstance(binding, Mapping):
            checkpoint_identity = {
                "kind": LOW_WEIGHT_ORACLE_KIND,
                "binding_sha256": binding.get("binding_sha256"),
            }
            failures.extend(
                _sat_backend_terminal_failures(
                    raw,
                    check_matrix,
                    target_logicals,
                    max_weight=threshold,
                    sector=normalized_sector,
                    checkpoint_identity=checkpoint_identity,
                )
            )
    return failures


def _seal_oracle_evidence(evidence: dict[str, Any]) -> dict[str, Any]:
    unsigned = dict(evidence)
    unsigned.pop("evidence_sha256", None)
    evidence["evidence_sha256"] = _canonical_json_sha256(unsigned)
    return evidence


def _combined_oracle_evidence(
    sectors: Mapping[str, Mapping[str, Any]],
    *,
    logical_detector: Mapping[str, Any],
    threshold: int,
    elapsed_s: float,
) -> dict[str, Any]:
    """Seal one top-level decision from independently resumable sectors."""

    copied_sectors = {
        sector: json.loads(json.dumps(
            evidence,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ))
        for sector, evidence in sectors.items()
    }
    sat_sector = next(
        (
            sector
            for sector in ("X", "Z")
            if copied_sectors.get(sector, {}).get("outcome") == "SAT"
        ),
        None,
    )
    if sat_sector is not None:
        outcome = "SAT"
        witness = copied_sectors[sat_sector]["witness"]
        lower_bound = None
    elif len(copied_sectors) == 2 and all(
        copied_sectors[sector].get("outcome") == "UNSAT"
        for sector in ("X", "Z")
    ):
        outcome = "UNSAT"
        witness = None
        lower_bound = threshold + 1
    else:
        outcome = "UNKNOWN"
        witness = None
        lower_bound = None
    return _seal_oracle_evidence({
        "schema_version": LOW_WEIGHT_ORACLE_SCHEMA_VERSION,
        "kind": LOW_WEIGHT_ORACLE_KIND,
        "source_sha256": _SOURCE_SHA256,
        "outcome": outcome,
        "decision_complete": outcome in {"SAT", "UNSAT"},
        "retryable": outcome == "UNKNOWN",
        "max_weight": threshold,
        "distance_lower_bound": lower_bound,
        "witness": witness,
        "sectors": copied_sectors,
        "logical_detector": json.loads(json.dumps(
            logical_detector,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )),
        "message": None,
        "elapsed_s": float(elapsed_s),
    })


def _timeout_sector_evidence(
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    max_weight: int,
    sector: str,
) -> dict[str, Any]:
    """Return source/matrix-bound retry metadata when no sector time remains."""

    engine = (
        LOW_WEIGHT_MITM_ENGINE
        if max_weight <= LOW_WEIGHT_MITM_MAX_THRESHOLD
        else LOW_WEIGHT_SAT_ENGINE
    )
    return _seal_sector_evidence({
        "schema_version": LOW_WEIGHT_ORACLE_SCHEMA_VERSION,
        "kind": LOW_WEIGHT_SECTOR_KIND,
        "outcome": "UNKNOWN",
        "decision_complete": False,
        "retryable": True,
        "binding": _sector_binding(
            checks,
            logicals,
            threshold=max_weight,
            sector=sector,
            engine=engine,
        ),
        "max_weight": int(max_weight),
        "witness": None,
        "message": "oracle rung wall budget was exhausted before this sector",
        "elapsed_s": 0.0,
    })


def evaluate_css_low_weight_oracle(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    max_weight: int,
    hard_timeout_s: float = 30.0,
    terminal_sectors: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Evaluate both CSS sectors with strict SAT/UNSAT/UNKNOWN semantics.

    ``hard_timeout_s`` is a shared inner deadline, not a fresh budget for each
    sector.  The caller still owns a killable whole-rung wall around logical
    construction, MITM, and native solver code.  Source/matrix-bound terminal
    sectors from a prior UNKNOWN attempt may be supplied so only the missing
    sector is recomputed.
    """

    if isinstance(max_weight, bool) or not isinstance(
        max_weight, (int, np.integer)
    ):
        raise ValueError("max_weight must be an integer")
    threshold = int(max_weight)
    if threshold < 0:
        raise ValueError("max_weight must be nonnegative")
    timeout = float(hard_timeout_s)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("hard_timeout_s must be positive and finite")
    started = time.monotonic()
    logical_detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if logical_detector.get("verified") is not True:
        return _seal_oracle_evidence({
            "schema_version": LOW_WEIGHT_ORACLE_SCHEMA_VERSION,
            "kind": LOW_WEIGHT_ORACLE_KIND,
            "source_sha256": _SOURCE_SHA256,
            "outcome": "UNKNOWN",
            "decision_complete": False,
            "retryable": True,
            "max_weight": threshold,
            "distance_lower_bound": None,
            "witness": None,
            "sectors": {},
            "logical_detector": logical_detector,
            "message": "CSS logical detector completeness replay failed",
            "elapsed_s": time.monotonic() - started,
        })
    matrices = {
        sector: _validated_sector_problem(
            *css_sector_matrices(hx, hz, lx, lz, sector),
            max_weight=threshold,
            sector=sector,
        )[:2]
        for sector in ("X", "Z")
    }
    sectors: dict[str, dict[str, Any]] = {}
    reusable = terminal_sectors if isinstance(terminal_sectors, Mapping) else {}
    for sector in ("X", "Z"):
        checks, logicals = matrices[sector]
        cached_sector = reusable.get(sector)
        if (
            isinstance(cached_sector, Mapping)
            and cached_sector.get("outcome") in {"SAT", "UNSAT"}
        ):
            partial = _combined_oracle_evidence(
                {sector: cached_sector},
                logical_detector=logical_detector,
                threshold=threshold,
                elapsed_s=time.monotonic() - started,
            )
            if not verify_css_low_weight_oracle(
                partial,
                hx,
                hz,
                lx,
                lz,
                replay_mitm_unsat=False,
            ):
                sectors[sector] = dict(partial["sectors"][sector])
                if sectors[sector]["outcome"] == "SAT":
                    break
                continue
        remaining = timeout - (time.monotonic() - started)
        if remaining <= 0:
            sectors[sector] = _timeout_sector_evidence(
                checks,
                logicals,
                max_weight=threshold,
                sector=sector,
            )
            continue
        sectors[sector] = _solve_sector(
            checks,
            logicals,
            max_weight=threshold,
            sector=sector,
            hard_timeout_s=remaining,
        )
        if sectors[sector]["outcome"] == "SAT":
            break
    return _combined_oracle_evidence(
        sectors,
        logical_detector=logical_detector,
        threshold=threshold,
        elapsed_s=time.monotonic() - started,
    )


def _verify_normalized_witness(
    witness: Any,
    *,
    checks: np.ndarray,
    logicals: np.ndarray,
    sector: str,
    threshold: int,
) -> list[str]:
    if not isinstance(witness, Mapping):
        return ["SAT evidence has no normalized witness"]
    failures: list[str] = []
    bits = witness.get("bits")
    if (
        not isinstance(bits, list)
        or len(bits) != checks.shape[1]
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
    ):
        return ["normalized witness bits are invalid"]
    vector = np.asarray(bits, dtype=np.uint8)
    weight = int(vector.sum())
    syndrome = ((logicals @ vector) & 1).astype(int).tolist()
    if witness.get("side") != sector:
        failures.append("normalized witness has wrong sector")
    if witness.get("weight") != weight or not 1 <= weight <= threshold:
        failures.append("normalized witness weight is invalid")
    if np.any((checks @ vector) & 1):
        failures.append("normalized witness has nonzero check syndrome")
    if not any(syndrome):
        failures.append("normalized witness is logically trivial")
    if witness.get("logical_syndrome") != syndrome:
        failures.append("normalized logical syndrome mismatch")
    expected_index = next((i for i, bit in enumerate(syndrome) if bit), None)
    if witness.get("index") != expected_index:
        failures.append("normalized witness logical index mismatch")
    if witness.get("support") != [int(i) for i in np.flatnonzero(vector)]:
        failures.append("normalized witness support mismatch")
    return failures


def verify_css_low_weight_oracle(
    evidence: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    require_current_source: bool = True,
    replay_mitm_unsat: bool = True,
) -> list[str]:
    """Replay identities and every SAT witness in an oracle artifact.

    This verifies a negative witness without trusting solver metadata. Setting
    ``require_current_source=False`` is deliberately restricted to top-level
    ``SAT`` upper-bound witnesses; historical ``UNSAT`` lower bounds remain
    fail-closed. Callers requiring an independent lower-bound replay should
    invoke :func:`evaluate_css_low_weight_oracle` again or proceed to the
    formal certificate stages.

    ``replay_mitm_unsat=False`` is reserved for the private, source-bound
    Stage-1 run ledger. Publication and external verification must retain the
    default and independently rerun deterministic MITM UNSAT decisions.
    """

    if type(replay_mitm_unsat) is not bool:
        raise TypeError("replay_mitm_unsat must be a boolean")

    failures: list[str] = []
    if not isinstance(evidence, Mapping):
        return ["oracle evidence is not an object"]
    unsigned = dict(evidence)
    stored_sha256 = unsigned.pop("evidence_sha256", None)
    try:
        actual_sha256 = _canonical_json_sha256(unsigned)
    except (TypeError, ValueError):
        return ["oracle evidence is not strict JSON"]
    if stored_sha256 != actual_sha256:
        failures.append("oracle evidence self-hash mismatch")
    if (
        evidence.get("schema_version") != LOW_WEIGHT_ORACLE_SCHEMA_VERSION
        or evidence.get("kind") != LOW_WEIGHT_ORACLE_KIND
        or evidence.get("outcome") not in LOW_WEIGHT_OUTCOMES
    ):
        failures.append("oracle evidence schema/outcome is invalid")
        return failures
    declared_source = evidence.get("source_sha256")
    declared_source_valid = bool(
        isinstance(declared_source, str)
        and len(declared_source) == 64
        and not any(
            character not in "0123456789abcdef"
            for character in declared_source
        )
    )
    if not declared_source_valid:
        failures.append("oracle evidence source binding is invalid")
    elif require_current_source and declared_source != _SOURCE_SHA256:
        failures.append("oracle evidence source binding mismatch")
    if (
        not isinstance(declared_source, str)
        or not declared_source_valid
    ):
        declared_source = _SOURCE_SHA256
    threshold = evidence.get("max_weight")
    if isinstance(threshold, bool) or not isinstance(threshold, int) or threshold < 0:
        failures.append("oracle threshold is invalid")
        return failures

    current_detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if evidence.get("logical_detector") != current_detector:
        failures.append("oracle logical detector report does not replay")
    outcome = str(evidence.get("outcome"))
    if not require_current_source and outcome != "SAT":
        failures.append(
            "historical-source relaxation is restricted to SAT upper-bound "
            "witnesses"
        )
    if outcome in {"SAT", "UNSAT"} and current_detector.get("verified") is not True:
        failures.append("terminal oracle evidence has invalid logical detectors")

    sectors = evidence.get("sectors")
    if not isinstance(sectors, Mapping):
        failures.append("oracle sector evidence is missing")
        return failures
    if any(side not in {"X", "Z"} for side in sectors):
        failures.append("oracle sector evidence contains an invalid key")

    sector_outcomes: dict[str, str] = {}
    for sector in ("X", "Z"):
        if sector not in sectors:
            continue
        sector_evidence = sectors[sector]
        if not isinstance(sector_evidence, Mapping):
            failures.append(f"{sector} sector evidence is not an object")
            continue
        try:
            checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
            checks, logicals, _, _ = _validated_sector_problem(
                checks,
                logicals,
                max_weight=threshold,
                sector=sector,
            )
        except (TypeError, ValueError) as exc:
            failures.append(f"{sector} sector matrices are invalid: {exc}")
            continue
        sector_unsigned = dict(sector_evidence)
        sector_sha256 = sector_unsigned.pop("evidence_sha256", None)
        try:
            sector_hash_valid = sector_sha256 == _canonical_json_sha256(
                sector_unsigned
            )
        except (TypeError, ValueError):
            sector_hash_valid = False
        if not sector_hash_valid:
            failures.append(f"{sector} sector evidence self-hash mismatch")
        sector_outcome = sector_evidence.get("outcome")
        if sector_outcome not in LOW_WEIGHT_OUTCOMES:
            failures.append(f"{sector} sector outcome is invalid")
            continue
        sector_outcomes[sector] = str(sector_outcome)
        expected_complete = sector_outcome in {"SAT", "UNSAT"}
        if not (
            sector_evidence.get("schema_version")
            == LOW_WEIGHT_ORACLE_SCHEMA_VERSION
            and sector_evidence.get("kind") == LOW_WEIGHT_SECTOR_KIND
            and sector_evidence.get("max_weight") == threshold
            and sector_evidence.get("decision_complete") is expected_complete
            and sector_evidence.get("retryable") is (not expected_complete)
        ):
            failures.append(f"{sector} sector terminal/retry semantics are invalid")

        binding = sector_evidence.get("binding")
        engine = binding.get("engine") if isinstance(binding, Mapping) else None
        if engine not in {LOW_WEIGHT_MITM_ENGINE, LOW_WEIGHT_SAT_ENGINE}:
            failures.append(f"{sector} sector engine/binding is invalid")
        else:
            expected_binding = _sector_binding(
                checks,
                logicals,
                threshold=threshold,
                sector=sector,
                engine=str(engine),
                # Historical SAT witnesses remain algebraically replayable
                # after a source upgrade.  In that mode, preserve and verify
                # the artifact's own source identity instead of silently
                # rebinding it to the current implementation.  Search lower
                # bounds still use the default current-source mode.
                source_sha256=(
                    None
                    if require_current_source or not declared_source_valid
                    else declared_source
                ),
            )
            if dict(binding) != expected_binding:
                failures.append(f"{sector} sector matrix/source binding mismatch")
            if engine == LOW_WEIGHT_MITM_ENGINE and threshold > LOW_WEIGHT_MITM_MAX_THRESHOLD:
                failures.append(f"{sector} MITM threshold exceeds its complete range")
            if engine == LOW_WEIGHT_SAT_ENGINE and threshold <= LOW_WEIGHT_MITM_MAX_THRESHOLD:
                failures.append(f"{sector} SAT engine used inside the MITM range")

        if sector_outcome == "SAT":
            failures.extend(
                f"{sector}: {failure}"
                for failure in _verify_normalized_witness(
                    sector_evidence.get("witness"),
                    checks=checks,
                    logicals=logicals,
                    sector=sector,
                    threshold=threshold,
                )
            )
        elif sector_evidence.get("witness") is not None:
            failures.append(f"{sector} non-SAT evidence carries a witness")

        if (
            replay_mitm_unsat
            and engine == LOW_WEIGHT_MITM_ENGINE
            and sector_outcome == "UNSAT"
        ):
            replay = _solve_sector_mitm(
                checks,
                logicals,
                max_weight=threshold,
                sector=sector,
            )
            if replay.get("outcome") != "UNSAT":
                failures.append(f"{sector} MITM UNSAT does not replay")
        elif engine == LOW_WEIGHT_SAT_ENGINE and sector_outcome in {"SAT", "UNSAT"}:
            raw = sector_evidence.get("solver_evidence")
            if not isinstance(raw, Mapping):
                failures.append(f"{sector} SAT terminal evidence is missing")
            elif isinstance(binding, Mapping):
                checkpoint_identity = {
                    "kind": LOW_WEIGHT_ORACLE_KIND,
                    "binding_sha256": binding.get("binding_sha256"),
                }
                failures.extend(
                    f"{sector}: {failure}"
                    for failure in _sat_backend_terminal_failures(
                        raw,
                        checks,
                        logicals,
                        max_weight=threshold,
                        sector=sector,
                        checkpoint_identity=checkpoint_identity,
                    )
                )

    if outcome == "SAT":
        sat_sectors = [
            side for side in ("X", "Z") if sector_outcomes.get(side) == "SAT"
        ]
        if (
            not sat_sectors
            or evidence.get("decision_complete") is not True
            or evidence.get("retryable") is not False
            or evidence.get("distance_lower_bound") is not None
        ):
            failures.append("top-level SAT outcome lacks complete witness semantics")
        elif evidence.get("witness") != sectors[sat_sectors[0]].get("witness"):
            failures.append("top-level SAT witness disagrees with sector evidence")
    elif outcome == "UNSAT":
        if (
            sector_outcomes != {"X": "UNSAT", "Z": "UNSAT"}
            or evidence.get("decision_complete") is not True
            or evidence.get("retryable") is not False
            or evidence.get("distance_lower_bound") != threshold + 1
            or evidence.get("witness") is not None
        ):
            failures.append("top-level UNSAT does not contain two complete sectors")
    else:
        if (
            evidence.get("decision_complete") is not False
            or evidence.get("retryable") is not True
            or evidence.get("distance_lower_bound") is not None
            or evidence.get("witness") is not None
            or any(value == "SAT" for value in sector_outcomes.values())
        ):
            failures.append("top-level UNKNOWN has inconsistent sector semantics")
    return failures


def normalized_low_weight_witness(
    evidence: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> dict[str, Any] | None:
    """Return a copied replayed SAT witness, or ``None`` for non-SAT evidence."""

    failures = verify_css_low_weight_oracle(evidence, hx, hz, lx, lz)
    if failures:
        raise ValueError("invalid low-weight oracle evidence: " + "; ".join(failures))
    if evidence.get("outcome") != "SAT":
        return None
    return json.loads(json.dumps(evidence["witness"], allow_nan=False))


__all__ = [
    "LOW_WEIGHT_MITM_ENGINE",
    "LOW_WEIGHT_MITM_MAX_THRESHOLD",
    "LOW_WEIGHT_ORACLE_KIND",
    "LOW_WEIGHT_ORACLE_SCHEMA_VERSION",
    "LOW_WEIGHT_OUTCOMES",
    "evaluate_css_low_weight_oracle",
    "evaluate_low_weight_sector",
    "normalized_low_weight_witness",
    "verify_css_low_weight_oracle",
    "verify_low_weight_sector_evidence",
]
