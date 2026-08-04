"""Multi-stage evaluation cascade for bivariate bicycle code candidates.

This is the central evaluation module.  Every candidate polynomial pair
is assessed through a six-stage cascade that progressively invests more
compute in more promising candidates:

1. **Validate** (microseconds) -- Checks polynomial structure: 2-6
   distinct terms with exponents in range for the target lattice.
   See :func:`evaluation.bb_code.validate_terms`.

2. **Build & compute k** (milliseconds) -- Constructs a
   :class:`qldpc.codes.BBCode` and reads ``(n, k)`` via GF(2) rank.
   Rejects only codes with ``k = 0`` (stage ``k_zero``); every positive
   dimension remains eligible for the formal challenge.

3. **Challenge pre-filter** (milliseconds, optional) -- When
   ``challenge_target_fom`` is set, computes a symplectic-basis distance upper
   bound before any decoder work.  A replayable logical/dual witness whose
   weight is at or below the dynamic final-gate rejection cutoff proves that
   the candidate cannot win and terminates the cascade.

4. **Quick distance estimate** (seconds) -- Runs
   :func:`evaluation.distance.estimate_distance` with ``quick_trials``
   BP-OSD trials (default 100).  Codes with ``d <= 2`` are tagged
   ``trivial_distance`` and exit early.  Every decoder-only distance is
   explicitly an upper bound; it is never marked trusted or exact.

5. **Refined distance estimate** (seconds) -- Triggered when preliminary
   ``FOM >= fom_threshold_refine`` (default 6.0).  Runs 3 independent
   BP-OSD batches of ``refine_trials`` each and keeps the minimum.
   An additional OSD-CS order-10 verification pass
   (:func:`evaluation.distance.estimate_distance_osd_cs`) fires when
   ``FOM >= fom_threshold_osd_cs``.  OSD-CS has controls independent of the
   legacy exact stage.

6. **Exact distance** (minutes) -- Triggered when refined
   ``FOM >= fom_threshold_exact`` (default 8.0).  Calls
   :func:`evaluation.distance.compute_distance_exact` with a configurable
   timeout.  Returns ``None`` on timeout (stage ``exact_timeout``).

The cascade is orchestrated by :func:`evaluate_candidate`, which returns
a dict with keys ``n, k, d, d_is_exact, distance_trusted, fom,
encoding_rate, ell, m, A_terms, B_terms, score, stage``.

:func:`evaluate_batch` and :func:`evaluate_lattices` provide batch
wrappers for evaluating lists of candidates across one or many lattices.

Constants
---------
SCORE_REJECTED : float
    Score assigned to all rejected candidates (``-inf``).
DISTANCE_TRUST_RATIO : float
    Deprecated compatibility constant. Decoder-only distance is never trusted.
DISTANCE_UNTRUST_RATIO : float
    Deprecated compatibility constant. Decoder-only distance is never trusted.
"""

from __future__ import annotations

import copy
import hashlib
import json
import logging
import math
import os
import stat
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from evaluation.bb_code import build_bb_code, validate_terms, get_code_params_fast
from evaluation.geometry import candidate_geometry, normalize_geometry
from evaluation.distance import estimate_distance, estimate_distance_osd_cs, compute_distance_exact
from evaluation.distance_milp import (
    _implementation_fingerprint as _distance_milp_implementation_fingerprint,
    compute_distance_milp,
    get_code_matrices,
    symplectic_weight_bound,
    symplectic_weight_witness,
    write_symplectic_weight_checkpoint,
)
from evaluation.low_weight_oracle import (
    evaluate_css_low_weight_oracle,
    verify_css_low_weight_oracle,
)

logger = logging.getLogger(__name__)

SCORE_REJECTED = float("-inf")
_MILP_CACHE_KIND = "qcode-milp-search-cache-record"
_MILP_CACHE_SCHEMA_VERSION = 1
_MILP_CACHE_MAX_RECORD_BYTES = 4 * 1024 * 1024
try:
    _EVALUATOR_SOURCE_SHA256 = hashlib.sha256(
        Path(__file__).read_bytes()
    ).hexdigest()
except OSError:
    _EVALUATOR_SOURCE_SHA256 = None

# Deprecated compatibility exports.  Historical callers imported these
# empirical d/sqrt(n) boundaries, but evaluator results no longer use them:
# a decoder-found logical is an upper bound regardless of its ratio.
DISTANCE_TRUST_RATIO = 1.3
DISTANCE_UNTRUST_RATIO = 2.0


# The formal challenge accepts every positive dimension.  Keeping the old
# k>=4 heuristic here made k=1..3 candidates return before a proof checkpoint
# existed, so Humanize could neither seal nor retry them.
MIN_K_THRESHOLD = 1
SCORE_K_LOW_PENALTY = -1000.0


def compute_fom(n: int, k: int, d: int) -> float:
    """Compute figure of merit kd²/n."""
    if n == 0 or k == 0 or d == 0:
        return 0.0
    return k * d * d / n


def compute_fom_rejection_cutoff(n: int, k: int, target_fom: float) -> int:
    """Return the largest integer distance that cannot strictly beat a FOM target.

    A witnessed logical operator of weight ``d`` is a valid upper bound on the
    true distance and excludes ``FOM > target`` iff ``k*d² <= target*n``.
    The calculation is exact so equality at a boundary such as FOM 12 cannot
    be changed by floating-point rounding.
    """
    if n <= 0 or k <= 0:
        raise ValueError("n and k must be positive")
    try:
        target = Fraction(str(target_fom))
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError("target_fom must be a finite non-negative number") from exc
    if target < 0:
        raise ValueError("target_fom must be a finite non-negative number")
    squared_cutoff = (target.numerator * n) // (target.denominator * k)
    return math.isqrt(squared_cutoff)


def _validated_feasible_threshold_witness(
    details: dict, proof_distance: int
) -> dict:
    positive = []
    for name in ("d_x", "d_z"):
        value = details.get(name)
        if type(value) is not int or value < 0:
            raise RuntimeError(
                f"MILP feasible threshold proof has invalid {name}"
            )
        if value > 0:
            positive.append(value)
    if not positive or min(positive) != proof_distance:
        raise RuntimeError(
            "MILP direction distances disagree with threshold proof distance"
        )

    witness = details.get("minimum_direction_witness")
    required = {"side", "index", "weight", "bits"}
    if not isinstance(witness, dict) or set(witness) != required:
        raise RuntimeError(
            "MILP feasible threshold proof has no embedded minimum witness"
        )
    if witness.get("side") not in {"X", "Z"}:
        raise RuntimeError("MILP minimum witness has invalid side")
    if type(witness.get("index")) is not int or witness["index"] < 0:
        raise RuntimeError("MILP minimum witness has invalid index")
    if (
        type(witness.get("weight")) is not int
        or witness["weight"] != proof_distance
    ):
        raise RuntimeError("MILP minimum witness weight disagrees with distance")
    bits = witness.get("bits")
    if (
        not isinstance(bits, list)
        or len(bits) == 0
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
        or sum(bits) != proof_distance
    ):
        raise RuntimeError("MILP minimum witness bits are invalid")
    return copy.deepcopy(witness)


def compute_challenge_rejection_cutoff(
    n: int, k: int, target_fom: float
) -> int:
    """Return the largest distance proving that the final gate cannot pass.

    At the official scalar threshold, the challenge also has fixed-coordinate
    Pareto win rules. Those can admit a code that ties the scalar FOM at a
    smaller ``n``, so the Stage 1 cutoff must preserve them.
    """
    scalar_cutoff = compute_fom_rejection_cutoff(n, k, target_fom)
    from evaluation.final_gate import FOM_THRESHOLD, minimum_winning_distance

    if Fraction(str(target_fom)) != Fraction(str(FOM_THRESHOLD)):
        return scalar_cutoff
    try:
        minimum_passing = minimum_winning_distance(n, k)
    except ValueError:
        # No distance allowed by this block length can pass any final-gate rule.
        return min(scalar_cutoff, n)
    return min(scalar_cutoff, minimum_passing - 1)


def _annotate_challenge_target(
    result: dict,
    *,
    n: int,
    k: int,
    target_fom: float,
) -> None:
    """Attach exact dynamic final-gate cutoff metadata to ``result``."""
    scalar_cutoff = compute_fom_rejection_cutoff(n, k, target_fom)
    challenge_cutoff = compute_challenge_rejection_cutoff(n, k, target_fom)
    target = Fraction(str(target_fom))
    result.update({
        "challenge_prefilter_enabled": True,
        "fom_target": float(target_fom),
        "fom_target_numerator": target.numerator,
        "fom_target_denominator": target.denominator,
        "fom_rejection_cutoff": scalar_cutoff,
        "challenge_rejection_cutoff": challenge_cutoff,
        "minimum_passing_distance": challenge_cutoff + 1,
        "fom_target_excluded_by_upper_bound": False,
        "final_gate_excluded_by_upper_bound": False,
        "threshold_rejection_proven": False,
    })


def _validate_replayable_symplectic_witness(
    code: Any,
    witness: Any,
    *,
    distance: int,
) -> dict | None:
    """Replay a symplectic logical/dual witness against rebuilt matrices."""
    required = {
        "side",
        "index",
        "dual_side",
        "dual_index",
        "weight",
        "bits",
    }
    if not isinstance(witness, Mapping) or set(witness) != required:
        return None
    side = witness.get("side")
    dual_side = witness.get("dual_side")
    if (
        side not in {"X", "Z"}
        or dual_side != ("Z" if side == "X" else "X")
    ):
        return None
    for field in ("index", "dual_index", "weight"):
        if type(witness.get(field)) is not int:
            return None
    if (
        witness["index"] < 0
        or witness["dual_index"] < 0
        or witness["weight"] != distance
        or distance < 1
    ):
        return None
    bits = witness.get("bits")
    try:
        hx, hz, lx, lz = get_code_matrices(code)
        n = int(code.num_qudits)
    except Exception:
        return None
    if (
        not isinstance(bits, list)
        or len(bits) != n
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
        or sum(bits) != distance
    ):
        return None
    vector = np.asarray(bits, dtype=np.uint8)
    logicals, duals, checks = (
        (lx, lz, hz) if side == "X" else (lz, lx, hx)
    )
    matrices = (logicals, duals, checks)
    if any(
        not isinstance(matrix, np.ndarray)
        or matrix.ndim != 2
        or matrix.shape[1] != n
        for matrix in matrices
    ):
        return None
    if (
        witness["index"] >= logicals.shape[0]
        or witness["dual_index"] >= duals.shape[0]
    ):
        return None
    logical = np.asarray(
        logicals[witness["index"]], dtype=np.uint8
    ).reshape(-1) % 2
    dual = np.asarray(
        duals[witness["dual_index"]], dtype=np.uint8
    ).reshape(-1) % 2
    if not np.array_equal(logical, vector):
        return None
    if np.any((np.asarray(checks, dtype=np.uint8) @ vector) % 2):
        return None
    if int(np.dot(dual, vector) % 2) != 1:
        return None
    return copy.deepcopy(dict(witness))


def _validate_replayable_css_witness(
    code: Any,
    witness: Any,
    *,
    distance: int,
) -> dict | None:
    """Replay a CSS logical witness produced by a MILP incumbent."""
    required = {"side", "index", "weight", "bits"}
    if not isinstance(witness, Mapping) or set(witness) != required:
        return None
    side = witness.get("side")
    index = witness.get("index")
    weight = witness.get("weight")
    bits = witness.get("bits")
    try:
        hx, hz, lx, lz = get_code_matrices(code)
        n = int(code.num_qudits)
    except Exception:
        return None
    if (
        side not in {"X", "Z"}
        or type(index) is not int
        or index < 0
        or type(weight) is not int
        or weight != distance
        or not isinstance(bits, list)
        or len(bits) != n
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
        or sum(bits) != distance
    ):
        return None
    vector = np.asarray(bits, dtype=np.uint8)
    checks, duals = (hz, lz) if side == "X" else (hx, lx)
    if (
        not isinstance(checks, np.ndarray)
        or checks.ndim != 2
        or checks.shape[1] != n
        or not isinstance(duals, np.ndarray)
        or duals.ndim != 2
        or duals.shape[1] != n
        or index >= duals.shape[0]
    ):
        return None
    if np.any((np.asarray(checks, dtype=np.uint8) @ vector) % 2):
        return None
    if int(np.dot(np.asarray(duals[index], dtype=np.uint8), vector) % 2) != 1:
        return None
    return copy.deepcopy(dict(witness))


def _record_distance_upper_bound(
    result: dict,
    *,
    n: int,
    k: int,
    distance: int,
    source: str,
    stage: str,
) -> bool:
    """Record a scalar decoder upper bound without granting distance credit.

    BP/OSD returns only a number here, not the logical-operator bits needed to
    replay the bound.  Consequently this helper *never* makes a candidate a
    terminal negative, even when the number is below a challenge cutoff.  A
    caller may stop only after independently validating a replayable witness
    (or obtaining an exact distance).

    The Boolean return is true only when the scalar conflicts with an earlier
    proved lower bound, telling the cascade to stop with retry/zero credit.
    """
    distance = _positive_distance_bound(distance)
    if distance is None:
        raise ValueError(
            "distance upper bounds must be finite positive integers"
        )
    lower_bound = result.get("distance_lower_bound")
    if (
        result.get("distance_lower_bound_proven") is True
        and type(lower_bound) is int
        and distance < lower_bound
    ):
        _distance_backend_retry(
            result,
            source="distance_evidence_conflict",
            error=ValueError(
                f"{source} upper bound {distance} is below proved lower "
                f"bound {lower_bound}"
            ),
        )
        result["distance_evidence_conflict"] = {
            "upper_bound": distance,
            "upper_bound_source": source,
            "proved_lower_bound": lower_bound,
            "lower_bound_source": "low_weight_oracle",
        }
        return True
    upper_fom = compute_fom(n, k, distance)
    result.update({
        "d": distance,
        "d_is_exact": False,
        "distance_trusted": False,
        "distance_status": "upper_bound",
        "distance_upper_bound": distance,
        "distance_upper_bound_source": source,
        # Keep the legacy ``fom`` projection for reporting compatibility, but
        # make its upper-bound semantics explicit and grant it no score.
        "fom": upper_fom,
        "fom_upper_bound": upper_fom,
        "fitness_distance_credit": 0.0,
        "score": 0.0,
        "stage": stage,
        "search_status": (
            "certified_lower_bound"
            if result.get("distance_lower_bound_proven") is True
            else "unresolved"
        ),
    })
    return False


def _is_exact_distance_result(result: Mapping[str, Any]) -> bool:
    """Return whether a public result may receive positive distance credit."""
    return (
        result.get("d_is_exact") is True
        and result.get("distance_status") != "upper_bound"
    )


def _result_ranking_score(result: Mapping[str, Any]) -> float:
    """Return a proof-safe public ranking score.

    ``quick_k_only`` is an explicitly distance-free screening mode, so its
    encoding-rate proxy remains useful.  In every distance-evaluation mode,
    only exact results may rank positively.  This second-line normalization
    also protects batch callers that provide legacy or mocked rows whose raw
    ``score`` still contains an upper-bound FOM.
    """
    raw = result.get("score", 0.0)
    try:
        score = float(raw)
    except (TypeError, ValueError, OverflowError):
        return SCORE_REJECTED
    if not math.isfinite(score):
        return score if score < 0 else 0.0
    if result.get("stage") == "quick_k_only":
        return score
    if _is_exact_distance_result(result):
        return max(0.0, score)
    return min(0.0, score)


def _positive_distance_bound(value: Any) -> int | None:
    """Return a backend distance only when it is a finite positive integer.

    Distance backends occasionally fail by returning a sentinel ``0`` or a
    non-finite float rather than raising.  Neither is a logical-operator
    witness, and coercing either into an upper bound can incorrectly turn a
    retryable candidate into a terminal negative.
    """
    if isinstance(value, (bool, np.bool_)):
        return None
    try:
        numeric = float(value)
    except (TypeError, ValueError, OverflowError):
        return None
    if not math.isfinite(numeric) or numeric <= 0 or not numeric.is_integer():
        return None
    return int(numeric)


def _distance_backend_retry(
    result: dict,
    *,
    source: str,
    value: Any = None,
    error: Exception | None = None,
) -> dict:
    """Fail closed after a malformed/failed distance-backend invocation.

    Clear every provisional upper bound and proof/rejection marker so callers
    cannot mistake an incomplete cascade for either a survivor or a proven
    negative.  ``search_status=retry`` deliberately keeps the candidate out of
    fitness while making the incomplete evaluation explicit.
    """
    if error is None:
        error_type = "InvalidDistanceUpperBound"
        try:
            rendered = repr(value)
        except Exception:
            rendered = "<unrepresentable>"
        message = f"{source} returned non-positive/non-finite bound {rendered}"
    else:
        error_type = type(error).__name__
        try:
            message = str(error)
        except Exception:
            message = "<exception message unavailable>"
    for field in (
        "distance_upper_bound_source",
        "bp_distance_upper_bound",
        "osd_cs_distance_upper_bound",
        "d_symplectic",
        "d_x_symplectic",
        "d_z_symplectic",
        "symplectic_weight_witness",
        "threshold_proof_witness",
        "threshold_proof_distance",
        "threshold_proof_source",
        "threshold_proof_lhs",
        "threshold_proof_rhs",
        "search_rejection_source",
        "search_final_gate_excluded_by_upper_bound",
    ):
        result.pop(field, None)
    result.update({
        "d": 0,
        "d_is_exact": False,
        "distance_trusted": False,
        "distance_status": "unknown_backend_error",
        "distance_upper_bound": None,
        "fom": 0.0,
        "fom_upper_bound": None,
        "exact_distance": None,
        "exact_fom": None,
        "fitness_distance_credit": 0.0,
        "score": 0.0,
        "stage": f"{source}_retry",
        "search_status": "retry",
        "distance_retry_required": True,
        "distance_backend_error": {
            "source": source,
            "type": error_type[:256],
            "message": message[:1024],
        },
        "fom_target_excluded_by_upper_bound": False,
        "final_gate_excluded_by_upper_bound": False,
        "threshold_rejection_proven": False,
    })
    return result


def _make_result_template(
    ell: int, m: int, A_terms: list, B_terms: list, *, geometry=None,
) -> dict:
    """Create a default result dict for a candidate."""
    result = {
        "ell": ell,
        "m": m,
        "A_terms": A_terms,
        "B_terms": B_terms,
        "n": 2 * ell * m,
        "k": 0,
        "d": 0,
        "d_is_exact": False,
        "distance_trusted": False,
        "distance_status": "unknown",
        "distance_upper_bound": None,
        "fom_upper_bound": None,
        "exact_distance": None,
        "exact_fom": None,
        "fitness_distance_credit": 0.0,
        "search_status": "unresolved",
        "fom": 0.0,
        "encoding_rate": 0.0,
        "score": SCORE_REJECTED,
        "stage": "rejected",
    }
    canonical_geometry = normalize_geometry(ell, m, geometry)
    if canonical_geometry is not None:
        result["geometry"] = canonical_geometry
    return result


def _validate_and_build(
    ell: int,
    m: int,
    A_terms: list,
    B_terms: list,
    result: dict,
    *,
    geometry=None,
    apply_self_dual_gate: bool = True,
) -> tuple | None:
    """Validate terms, build code, compute k, apply early-exit rules.

    Returns (code, n, k) on success, or None if the candidate was rejected
    (result dict is updated in place with the rejection reason).
    """
    # Stage 1: Validate inputs
    try:
        validate_terms(ell, m, A_terms, "A")
        validate_terms(ell, m, B_terms, "B")
    except ValueError as e:
        logger.debug("Validation failed: %s", e)
        result["stage"] = "invalid"
        return None

    # Stage 2: Build code, compute k
    try:
        code = build_bb_code(
            ell, m, A_terms, B_terms, geometry=geometry,
        )
        n, k = get_code_params_fast(code)
    except Exception as e:
        logger.debug("Construction failed: %s", e)
        result["stage"] = "construction_error"
        return None

    result["n"] = n
    result["k"] = k
    result["encoding_rate"] = k / n if n > 0 else 0.0

    if k == 0:
        result["stage"] = "k_zero"
        return None
    if k < MIN_K_THRESHOLD:
        result["stage"] = "k_low"
        result["score"] = SCORE_K_LOW_PENALTY + k
        return None

    # Self-dual gate: BB codes with A=B always have d=2 (proven).
    # BP-OSD misses this in 29/30 batches, so we hard-code it.
    if (
        apply_self_dual_gate
        and sorted(tuple(t) for t in A_terms)
        == sorted(tuple(t) for t in B_terms)
    ):
        result["d"] = 2
        result["d_is_exact"] = True
        result["distance_trusted"] = True
        result["distance_status"] = "exact"
        result["distance_upper_bound"] = 2
        result["distance_upper_bound_source"] = "self_dual_exact"
        result["fom"] = k * 4 / n
        result["fom_upper_bound"] = result["fom"]
        result["exact_distance"] = 2
        result["exact_fom"] = result["fom"]
        result["fitness_distance_credit"] = result["exact_fom"]
        result["search_status"] = "exact"
        result["score"] = result["fom"]
        result["stage"] = "self_dual_d2"
        return None

    return code, n, k


def evaluate_candidate(
    ell: int,
    m: int,
    A_terms: list[tuple[int, int]],
    B_terms: list[tuple[int, int]],
    *,
    geometry=None,
    quick: bool = False,
    fom_threshold_refine: float = 6.0,
    fom_threshold_exact: float = 8.0,
    fom_threshold_osd_cs: float | None = None,
    quick_trials: int = 100,
    refine_trials: int = 500,
    osd_cs_trials: int = 200,
    exact_timeout: int = 300,
    skip_exact: bool = False,
    skip_osd_cs: bool = False,
    challenge_target_fom: float | None = None,
    low_weight_oracle_max_weight: int | None = None,
    low_weight_oracle_hard_timeout_s: float = 30.0,
) -> dict:
    """Evaluate a BB code candidate through the full cascade.

    Args:
        ell: Cyclic group order for x.
        m: Cyclic group order for y.
        A_terms: 3 exponent pairs for polynomial A.
        B_terms: 3 exponent pairs for polynomial B.
        quick: If True, only compute k (skip distance).
        fom_threshold_refine: FOM threshold to trigger refined distance estimation.
        fom_threshold_exact: FOM threshold to trigger exact distance computation.
        fom_threshold_osd_cs: Independent FOM threshold for OSD-CS. ``None``
            preserves the legacy behaviour by using ``fom_threshold_exact``.
        quick_trials: Number of BP-OSD trials for initial estimate.
        refine_trials: Number of BP-OSD trials for refined estimate.
        osd_cs_trials: Number of OSD-CS trials.
        exact_timeout: Timeout in seconds for exact distance computation.
        skip_exact: Skip legacy brute-force exact without disabling OSD-CS.
        skip_osd_cs: Explicitly skip the OSD-CS upper-bound stage.
        challenge_target_fom: Optional challenge objective. Before BP-OSD,
            reject candidates for which a replayable symplectic logical witness
            proves that the dynamic final-gate distance cutoff cannot be met.
        low_weight_oracle_max_weight: Optional complete X/Z low-weight query.
            The actual threshold is the smaller of this cap and the dynamic
            challenge rejection cutoff. A replayed SAT witness rejects; only
            two complete UNSAT sectors provide positive lower-bound fitness.
        low_weight_oracle_hard_timeout_s: Per-sector hard wall used when the
            oracle delegates thresholds above its deterministic MITM range to
            the optional SAT backend.

    Returns:
        Dict with keys: n, k, d, d_is_exact, fom, encoding_rate,
        ell, m, A_terms, B_terms, score, stage.
    """
    geometry = normalize_geometry(ell, m, geometry)
    result = _make_result_template(
        ell, m, A_terms, B_terms, geometry=geometry,
    )

    built = _validate_and_build(
        ell, m, A_terms, B_terms, result, geometry=geometry,
    )
    if built is None:
        if challenge_target_fom is not None and result["d_is_exact"]:
            _annotate_challenge_target(
                result,
                n=result["n"],
                k=result["k"],
                target_fom=challenge_target_fom,
            )
            if result["d"] <= result["challenge_rejection_cutoff"]:
                result["search_status"] = "terminal_negative"
                result["threshold_rejection_proven"] = True
                result["final_gate_excluded_by_upper_bound"] = True
                result["fitness_distance_credit"] = 0.0
                result["score"] = 0.0
        return result
    code, n, k = built

    if quick:
        result["stage"] = "quick_k_only"
        result["score"] = k / n  # use encoding rate as proxy
        return result

    # Optional challenge pre-filter: a symplectic-basis row is a valid distance
    # upper bound, but only a replayable logical/dual witness may terminate the
    # search.  If witness construction fails, fail open into BP-OSD and do not
    # claim a formal rejection.
    challenge_symplectic_upper: int | None = None
    if challenge_target_fom is not None:
        _annotate_challenge_target(
            result,
            n=n,
            k=k,
            target_fom=challenge_target_fom,
        )
        try:
            raw_symplectic = symplectic_weight_bound(code)
        except Exception as exc:
            logger.exception(
                "Challenge symplectic pre-filter failed; retrying candidate"
            )
            return _distance_backend_retry(
                result, source="symplectic_upper_bound", error=exc
            )
        else:
            try:
                raw_d_symp, raw_d_x_symp, raw_d_z_symp = raw_symplectic
            except (TypeError, ValueError):
                raw_d_symp = raw_d_x_symp = raw_d_z_symp = None
            d_symp = _positive_distance_bound(raw_d_symp)
            d_x_symp = _positive_distance_bound(raw_d_x_symp)
            d_z_symp = _positive_distance_bound(raw_d_z_symp)
            if None in (d_symp, d_x_symp, d_z_symp):
                logger.warning(
                    "Challenge symplectic pre-filter returned invalid bounds "
                    "%r; retrying candidate",
                    raw_symplectic,
                )
                return _distance_backend_retry(
                    result,
                    source="symplectic_upper_bound",
                    value=raw_symplectic,
                )
            else:
                challenge_symplectic_upper = d_symp
                result.update({
                    "d_symplectic": d_symp,
                    "d_x_symplectic": d_x_symp,
                    "d_z_symplectic": d_z_symp,
                })
            if (
                challenge_symplectic_upper is not None
                and challenge_symplectic_upper
                <= result["challenge_rejection_cutoff"]
            ):
                try:
                    raw_witness = symplectic_weight_witness(
                        code, challenge_symplectic_upper
                    )
                except Exception:
                    logger.exception(
                        "Failed to construct challenge symplectic witness; "
                        "continuing to BP-OSD"
                    )
                    raw_witness = None
                witness = _validate_replayable_symplectic_witness(
                    code,
                    raw_witness,
                    distance=challenge_symplectic_upper,
                )
                if witness is None:
                    logger.warning(
                        "Challenge symplectic upper bound d=%s has no "
                        "replayable logical/dual witness; refusing rejection",
                        challenge_symplectic_upper,
                    )
                    # A basis weight without a replayable logical/dual witness
                    # is not allowed to influence any later BP/OSD decision.
                    challenge_symplectic_upper = None
                    for field in (
                        "d_symplectic",
                        "d_x_symplectic",
                        "d_z_symplectic",
                    ):
                        result.pop(field, None)
                    result["symplectic_prefilter_error"] = {
                        "type": "UnreplayableSymplecticWitness",
                        "message": (
                            "symplectic upper bound had no replayable "
                            "logical/dual witness"
                        ),
                    }
                else:
                    upper_fom = compute_fom(
                        n, k, challenge_symplectic_upper
                    )
                    result.update({
                        "d": challenge_symplectic_upper,
                        "d_is_exact": False,
                        "distance_trusted": False,
                        "distance_status": "upper_bound",
                        "distance_upper_bound": challenge_symplectic_upper,
                        "distance_upper_bound_source": (
                            "symplectic_upper_bound"
                        ),
                        "fom": upper_fom,
                        "fom_upper_bound": upper_fom,
                        "score": 0.0,
                        "stage": "challenge_symplectic_rejected",
                        "search_status": "terminal_negative",
                        "fitness_distance_credit": 0.0,
                        "fom_target_excluded_by_upper_bound": (
                            challenge_symplectic_upper
                            <= result["fom_rejection_cutoff"]
                        ),
                        "final_gate_excluded_by_upper_bound": True,
                        "threshold_rejection_proven": True,
                        "threshold_proof_distance": (
                            challenge_symplectic_upper
                        ),
                        "threshold_proof_source": "symplectic_upper_bound",
                        "symplectic_weight_witness": copy.deepcopy(witness),
                        "threshold_proof_witness": copy.deepcopy(witness),
                    })
                    result["threshold_proof_lhs"] = (
                        k
                        * challenge_symplectic_upper
                        * challenge_symplectic_upper
                        * result["fom_target_denominator"]
                    )
                    result["threshold_proof_rhs"] = (
                        result["fom_target_numerator"] * n
                    )
                    return result

    # Proof-safe low-weight search signal.  Unlike BP/OSD, a two-sector UNSAT
    # decision proves a real lower bound.  SAT is useful in the opposite
    # direction: its independently replayed operator rejects the candidate and
    # supplies concrete X/Z failure geometry to the mutation loop.  UNKNOWN is
    # never allowed to fall through into a survivor score.
    if low_weight_oracle_max_weight is not None:
        if challenge_target_fom is None:
            raise ValueError(
                "low_weight_oracle_max_weight requires challenge_target_fom"
            )
        if (
            isinstance(low_weight_oracle_max_weight, bool)
            or not isinstance(low_weight_oracle_max_weight, int)
            or low_weight_oracle_max_weight < 0
        ):
            raise ValueError(
                "low_weight_oracle_max_weight must be a nonnegative integer"
            )
        oracle_threshold = min(
            low_weight_oracle_max_weight,
            int(result["challenge_rejection_cutoff"]),
        )
        try:
            hx, hz, lx, lz = get_code_matrices(code)
            oracle = evaluate_css_low_weight_oracle(
                hx,
                hz,
                lx,
                lz,
                max_weight=oracle_threshold,
                hard_timeout_s=low_weight_oracle_hard_timeout_s,
            )
            oracle_failures = verify_css_low_weight_oracle(
                oracle, hx, hz, lx, lz
            )
        except Exception as exc:
            return _distance_backend_retry(
                result, source="low_weight_oracle", error=exc
            )
        if oracle_failures:
            return _distance_backend_retry(
                result,
                source="low_weight_oracle",
                value={"verification_failures": oracle_failures},
            )
        result["low_weight_oracle_threshold"] = oracle_threshold
        result["low_weight_oracle"] = oracle
        oracle_outcome = oracle.get("outcome")
        if oracle_outcome == "SAT":
            raw_witness = oracle.get("witness")
            if not isinstance(raw_witness, Mapping):
                return _distance_backend_retry(
                    result,
                    source="low_weight_oracle",
                    value="SAT result has no witness",
                )
            proof_witness = {
                field: copy.deepcopy(raw_witness.get(field))
                for field in ("side", "index", "weight", "bits")
            }
            proof_distance = _positive_distance_bound(
                proof_witness.get("weight")
            )
            replayed = (
                None
                if proof_distance is None
                else _validate_replayable_css_witness(
                    code, proof_witness, distance=proof_distance
                )
            )
            if replayed is None or proof_distance > oracle_threshold:
                return _distance_backend_retry(
                    result,
                    source="low_weight_oracle",
                    value="normalized SAT witness failed CSS replay",
                )
            upper_fom = compute_fom(n, k, proof_distance)
            result.update({
                "d": proof_distance,
                "d_is_exact": False,
                "distance_trusted": False,
                "distance_status": "upper_bound",
                "distance_upper_bound": proof_distance,
                "distance_upper_bound_source": "low_weight_oracle",
                "fom": upper_fom,
                "fom_upper_bound": upper_fom,
                "fitness_distance_credit": 0.0,
                "score": 0.0,
                "stage": "low_weight_oracle_rejected",
                "search_status": "terminal_negative",
                "threshold_rejection_proven": True,
                "threshold_proof_source": "low_weight_oracle",
                "threshold_proof_distance": proof_distance,
                "threshold_proof_witness": replayed,
                "fom_target_excluded_by_upper_bound": (
                    proof_distance <= result["fom_rejection_cutoff"]
                ),
                "final_gate_excluded_by_upper_bound": True,
                "search_final_gate_excluded_by_upper_bound": True,
            })
            result["threshold_proof_lhs"] = (
                k
                * proof_distance
                * proof_distance
                * result["fom_target_denominator"]
            )
            result["threshold_proof_rhs"] = (
                result["fom_target_numerator"] * n
            )
            return result
        if oracle_outcome == "UNSAT":
            lower_bound = oracle.get("distance_lower_bound")
            if (
                isinstance(lower_bound, bool)
                or not isinstance(lower_bound, int)
                or lower_bound != oracle_threshold + 1
            ):
                return _distance_backend_retry(
                    result,
                    source="low_weight_oracle",
                    value="UNSAT result has an invalid lower bound",
                )
            result.update({
                "distance_lower_bound": lower_bound,
                "distance_lower_bound_proven": True,
                "distance_lower_bound_status": "search_oracle_proven",
                "fom_lower_bound": compute_fom(n, k, lower_bound),
                "search_status": "certified_lower_bound",
            })
        else:
            retry = _distance_backend_retry(
                result,
                source="low_weight_oracle",
                value={
                    "outcome": oracle_outcome,
                    "retryable": oracle.get("retryable"),
                },
            )
            retry["low_weight_oracle_threshold"] = oracle_threshold
            retry["low_weight_oracle"] = oracle
            return retry

    # Stage 3: Quick distance estimate
    try:
        raw_d_bp = estimate_distance(code, num_trials=quick_trials)
    except Exception as exc:
        return _distance_backend_retry(
            result, source="bp_osd_0", error=exc
        )
    d_bp = _positive_distance_bound(raw_d_bp)
    if d_bp is None:
        return _distance_backend_retry(
            result, source="bp_osd_0", value=raw_d_bp
        )
    result["bp_distance_upper_bound"] = d_bp
    d_upper = (
        min(d_bp, challenge_symplectic_upper)
        if challenge_symplectic_upper is not None
        else d_bp
    )
    upper_source = (
        "symplectic_upper_bound"
        if challenge_symplectic_upper is not None
        and challenge_symplectic_upper < d_bp
        else "bp_osd_0"
    )
    if d_upper <= 2:
        _record_distance_upper_bound(
            result,
            n=n,
            k=k,
            distance=d_upper,
            source=upper_source,
            stage="trivial_distance",
        )
        return result

    if _record_distance_upper_bound(
        result,
        n=n,
        k=k,
        distance=d_upper,
        source=upper_source,
        stage="quick_estimate",
    ):
        return result
    upper_fom = result["fom_upper_bound"]

    # Stage 4: Refined distance estimate for promising candidates.
    # Run 3 independent BP-OSD batches (OSD_0) and take the minimum to reduce
    # variance. BP-OSD is an upper bound, so min of multiple runs is
    # tighter and more stable.
    if upper_fom >= fom_threshold_refine:
        for _ in range(3):
            try:
                raw_d_refined = estimate_distance(
                    code, num_trials=refine_trials
                )
            except Exception as exc:
                return _distance_backend_retry(
                    result, source="bp_osd_0_refined", error=exc
                )
            d_refined = _positive_distance_bound(raw_d_refined)
            if d_refined is None:
                return _distance_backend_retry(
                    result,
                    source="bp_osd_0_refined",
                    value=raw_d_refined,
                )
            if d_refined < d_upper:
                d_upper = d_refined
                upper_source = "bp_osd_0_refined"
            result["bp_distance_upper_bound"] = min(
                result["bp_distance_upper_bound"],
                d_refined,
            )
        if _record_distance_upper_bound(
            result,
            n=n,
            k=k,
            distance=d_upper,
            source=upper_source,
            stage="refined_estimate",
        ):
            return result
        upper_fom = result["fom_upper_bound"]

    # Stage 4b: OSD-CS verification for top candidates.
    # OSD-CS order=10 finds tighter bounds than OSD_0 for 7 of 9 tested
    # codes (4-12 point improvements on high-k codes). One batch of 200
    # trials catches the worst overestimates before they pollute fitness.
    effective_osd_cs_threshold = (
        fom_threshold_exact
        if fom_threshold_osd_cs is None
        else fom_threshold_osd_cs
    )
    if not skip_osd_cs and upper_fom >= effective_osd_cs_threshold:
        try:
            raw_d_cs = estimate_distance_osd_cs(
                code, num_trials=osd_cs_trials
            )
        except Exception as exc:
            return _distance_backend_retry(
                result, source="bp_osd_cs", error=exc
            )
        d_cs = _positive_distance_bound(raw_d_cs)
        if d_cs is None:
            return _distance_backend_retry(
                result, source="bp_osd_cs", value=raw_d_cs
            )
        result["osd_cs_distance_upper_bound"] = d_cs
        if d_cs < d_upper:
            d_upper = d_cs
            upper_source = "bp_osd_cs"
            if _record_distance_upper_bound(
                result,
                n=n,
                k=k,
                distance=d_upper,
                source=upper_source,
                stage="osd_cs_upper_bound",
            ):
                return result
            upper_fom = result["fom_upper_bound"]

    # Stage 5: Exact distance for top candidates
    if upper_fom >= fom_threshold_exact and not skip_exact:
        d_exact = compute_distance_exact(code, timeout_seconds=exact_timeout)
        if d_exact is not None:
            lower_bound = result.get("distance_lower_bound")
            if (
                result.get("distance_lower_bound_proven") is True
                and type(lower_bound) is int
                and d_exact < lower_bound
            ):
                retry = _distance_backend_retry(
                    result,
                    source="distance_evidence_conflict",
                    error=ValueError(
                        f"exact distance {d_exact} is below proved lower "
                        f"bound {lower_bound}"
                    ),
                )
                retry["distance_evidence_conflict"] = {
                    "exact_distance": d_exact,
                    "proved_lower_bound": lower_bound,
                    "lower_bound_source": "low_weight_oracle",
                }
                return retry
            result["d"] = d_exact
            result["d_is_exact"] = True
            result["distance_trusted"] = True
            result["distance_status"] = "exact"
            result["distance_upper_bound"] = d_exact
            result["distance_upper_bound_source"] = "exact"
            result["fom"] = compute_fom(n, k, d_exact)
            result["fom_upper_bound"] = result["fom"]
            result["exact_distance"] = d_exact
            result["exact_fom"] = result["fom"]
            result["fitness_distance_credit"] = result["exact_fom"]
            result["search_status"] = "exact"
            result["score"] = result["fom"]
            result["stage"] = "exact"
            if (
                challenge_target_fom is not None
                and d_exact <= result["challenge_rejection_cutoff"]
            ):
                result["search_status"] = "terminal_negative"
                result["threshold_rejection_proven"] = True
                result["final_gate_excluded_by_upper_bound"] = True
                result["fitness_distance_credit"] = 0.0
                result["score"] = 0.0
        else:
            result["stage"] = "exact_timeout"

    return result


def _candidate_components(
    candidate: Any,
    *,
    ell: int,
    m: int,
) -> tuple[Any, Any, dict[str, Any] | None]:
    """Normalize a legacy A/B pair or an expanded geometry-aware record."""

    if isinstance(candidate, Mapping):
        if "ell" in candidate and int(candidate["ell"]) != int(ell):
            raise ValueError("candidate ell disagrees with its evaluation lattice")
        if "m" in candidate and int(candidate["m"]) != int(m):
            raise ValueError("candidate m disagrees with its evaluation lattice")
        geometry = candidate_geometry({
            **candidate,
            "ell": int(ell),
            "m": int(m),
        })
        return candidate["A_terms"], candidate["B_terms"], geometry
    if not isinstance(candidate, (list, tuple)) or len(candidate) != 2:
        raise TypeError(
            "candidate must be an A/B pair or a geometry-aware mapping"
        )
    return candidate[0], candidate[1], None


def evaluate_batch(
    ell: int,
    m: int,
    candidates: list[tuple[list[tuple[int, int]], list[tuple[int, int]]]],
    **kwargs,
) -> list[dict]:
    """Evaluate a batch of (A_terms, B_terms) candidates for a given lattice.

    Args:
        ell: Cyclic group order for x.
        m: Cyclic group order for y.
        candidates: List of (A_terms, B_terms) tuples, as returned by
            generate_candidates(ell, m).
        **kwargs: Passed to evaluate_candidate.

    Returns:
        List of result dicts, sorted by score descending.
    """
    results = []
    for candidate in candidates:
        A_terms, B_terms, geometry = _candidate_components(
            candidate, ell=ell, m=m,
        )
        result = evaluate_candidate(
            ell,
            m,
            A_terms,
            B_terms,
            geometry=geometry,
            **kwargs,
        )
        results.append(result)
        if _result_ranking_score(result) > 0:
            logger.info(
                "[[%d, %d, %d]] FOM=%.2f (stage=%s)",
                result["n"], result["k"], result["d"],
                result["fom"], result["stage"],
            )
    results.sort(key=_result_ranking_score, reverse=True)
    return results


def evaluate_lattices(
    lattices: list[tuple[int, int]],
    generate_fn,
    **kwargs,
) -> list[dict]:
    """Run evaluation across multiple lattice dimensions.

    Args:
        lattices: List of (ell, m) pairs to search.
        generate_fn: A function (ell, m) -> list of (A_terms, B_terms).
        **kwargs: Passed to evaluate_candidate.

    Returns:
        All results across all lattices, sorted by score descending.
    """
    all_results = []
    for ell, m in lattices:
        candidates = generate_fn(ell, m)
        logger.info(
            "Evaluating %d candidates for lattice (%d, %d), n=%d",
            len(candidates), ell, m, 2 * ell * m,
        )
        results = evaluate_batch(ell, m, candidates, **kwargs)
        all_results.extend(results)
    all_results.sort(key=_result_ranking_score, reverse=True)
    return all_results


# ── MILP-based evaluation (Campaign 4+) ─────────────────────────


def evaluate_candidate_milp(
    ell: int,
    m: int,
    A_terms: list[tuple[int, int]],
    B_terms: list[tuple[int, int]],
    *,
    geometry=None,
    quick: bool = False,
    milp_timeout_per_logical: int = 30,
    milp_total_timeout: int = 120,
    milp_early_stop: int | None = 4,
    milp_target_fom: float | None = None,
    milp_checkpoint_path: str | Path | None = None,
    milp_resume: bool = True,
    milp_hard_timeout_per_logical: float | None = None,
) -> dict:
    """Evaluate a BB code candidate using MILP for exact distance.

    Simplified 3-stage cascade (vs 5-stage BP-OSD cascade):
      1. Validate + build + compute k  (microseconds)
      2. Quick k-only return if quick=True  (microseconds)
      3. MILP exact distance  (sub-second for d≤4, seconds to minutes for d≥6)

    Incumbents and symplectic witnesses are valid upper bounds; ``d_is_exact``
    is true only when every required direction was proven or a structural rule
    applies.

    Args:
        ell: Cyclic group order for x.
        m: Cyclic group order for y.
        A_terms: 3 exponent pairs for polynomial A.
        B_terms: 3 exponent pairs for polynomial B.
        quick: If True, only compute k (skip distance).
        milp_timeout_per_logical: Timeout per individual ILP solve.
        milp_total_timeout: Total timeout for all logicals combined.
        milp_early_stop: Stop immediately when d ≤ this value.
        milp_target_fom: If set, derive a safe per-candidate early-stop cutoff
            from reconstructed n and k. At the official threshold this also
            preserves all final-gate Pareto win rules and supersedes the fixed
            ``milp_early_stop`` value.
        milp_checkpoint_path: Optional atomic per-direction checkpoint path.
        milp_resume: Reuse matching proven-optimal checkpoint directions and
            retry incomplete directions.
        milp_hard_timeout_per_logical: Optional parent-enforced wall deadline;
            each direction then runs in a reusable, terminable child process.

    Returns:
        Dict with keys: n, k, d, d_is_exact, distance_trusted, fom,
        encoding_rate, ell, m, A_terms, B_terms, score, stage, milp_details.
    """
    geometry = normalize_geometry(ell, m, geometry)
    result = _make_result_template(
        ell, m, A_terms, B_terms, geometry=geometry,
    )
    checkpoint_identity = {
        "family": "css-bb",
        "ell": int(ell),
        "m": int(m),
        "A_terms": sorted([list(map(int, term)) for term in A_terms]),
        "B_terms": sorted([list(map(int, term)) for term in B_terms]),
    }
    if geometry is not None:
        checkpoint_identity["geometry"] = geometry
    if (
        milp_checkpoint_path is not None
        and milp_hard_timeout_per_logical is not None
    ):
        result["audit_evaluator_invocation"] = {
            "schema_version": 2,
            "checkpoint_path": os.path.abspath(
                os.fspath(milp_checkpoint_path)
            ),
            "resume": milp_resume is True,
            "timeout_per_logical": milp_timeout_per_logical,
            "total_timeout": milp_total_timeout,
            "hard_timeout_per_logical": float(
                milp_hard_timeout_per_logical
            ),
        }

    built = _validate_and_build(
        ell,
        m,
        A_terms,
        B_terms,
        result,
        geometry=geometry,
        # A formal Stage 1 invocation must materialize immutable evidence.
        # Let the symplectic d=2 path below write that checkpoint instead of
        # returning early with an unsealable numeric claim.
        apply_self_dual_gate=milp_checkpoint_path is None,
    )
    if built is None:
        return result
    code, n, k = built

    effective_early_stop = milp_early_stop
    result["milp_solver_attempted"] = False
    if milp_target_fom is not None:
        scalar_cutoff = compute_fom_rejection_cutoff(n, k, milp_target_fom)
        challenge_cutoff = compute_challenge_rejection_cutoff(
            n, k, milp_target_fom
        )
        target = Fraction(str(milp_target_fom))
        # In target-aware Stage 1 mode this cutoff is authoritative. A larger
        # fixed cutoff could discard a valid Pareto winner; a smaller one would
        # forfeit the intended performance gain.
        effective_early_stop = challenge_cutoff
        result.update({
            "fom_target": float(milp_target_fom),
            "fom_target_numerator": target.numerator,
            "fom_target_denominator": target.denominator,
            "fom_rejection_cutoff": scalar_cutoff,
            "challenge_rejection_cutoff": challenge_cutoff,
            "minimum_passing_distance": challenge_cutoff + 1,
            "milp_early_stop_objective": "challenge_final_gate",
            "fom_target_excluded_by_upper_bound": False,
            "final_gate_excluded_by_upper_bound": False,
            "threshold_rejection_proven": False,
            "milp_early_stop_triggered": False,
        })
    result["milp_effective_early_stop"] = effective_early_stop

    # Symplectic weight: instant scalar upper bound from Gaussian elimination.
    # It is diagnostic until the corresponding logical/dual witness is replayed.
    try:
        raw_symplectic = symplectic_weight_bound(code)
        raw_d_symp, _, _ = raw_symplectic
    except Exception:
        logger.exception(
            "Symplectic upper-bound backend failed; continuing to MILP"
        )
        raw_d_symp = None
    d_symp = _positive_distance_bound(raw_d_symp)
    if d_symp is not None:
        result["d_symplectic"] = d_symp

    if quick:
        result["stage"] = "quick_k_only"
        result["score"] = k / n
        return result

    # Pre-filter using symplectic weight bound (instant, no MILP needed).
    # d_symp is an upper bound on d from Gaussian elimination.
    # - d_symp ≤ 2: provably exact (BB codes with k>0 have d ≥ 2)
    # - d_symp ≤ effective early_stop: this valid upper bound already proves
    #   that the configured search objective cannot win, so MILP can be skipped.
    symplectic_witness = None
    if (
        d_symp is not None
        and (
            d_symp <= 2
            or (
            effective_early_stop is not None
            and d_symp <= effective_early_stop
            )
        )
    ):
        try:
            raw_witness = symplectic_weight_witness(code, d_symp)
        except Exception:
            logger.exception(
                "Failed to construct a replayable symplectic witness; "
                "continuing to MILP"
            )
            raw_witness = None
        symplectic_witness = _validate_replayable_symplectic_witness(
            code,
            raw_witness,
            distance=d_symp,
        )
        if symplectic_witness is None:
            logger.warning(
                "Symplectic upper bound d=%s has no replayable logical/dual "
                "witness; refusing solver-free rejection",
                d_symp,
            )
        else:
            result["symplectic_weight_witness"] = copy.deepcopy(
                symplectic_witness
            )
    if symplectic_witness is not None:
        symplectic_exact = d_symp <= 2
        upper_fom = compute_fom(n, k, d_symp)
        result["d"] = d_symp
        result["d_is_exact"] = symplectic_exact  # BB k>0 implies d >= 2.
        result["distance_trusted"] = True  # Valid upper bound
        result["distance_status"] = (
            "exact" if result["d_is_exact"] else "upper_bound"
        )
        result["distance_upper_bound"] = d_symp
        result["distance_upper_bound_source"] = "symplectic_upper_bound"
        result["fom"] = upper_fom
        result["fom_upper_bound"] = upper_fom
        result["exact_distance"] = d_symp if symplectic_exact else None
        result["exact_fom"] = upper_fom if symplectic_exact else None
        result["fitness_distance_credit"] = (
            upper_fom if symplectic_exact else 0.0
        )
        result["score"] = upper_fom if symplectic_exact else 0.0
        result["search_status"] = (
            "exact" if symplectic_exact else "terminal_negative"
        )
        result["stage"] = "symplectic_low_d"
        if milp_target_fom is not None:
            result["fom_target_excluded_by_upper_bound"] = (
                d_symp <= result["fom_rejection_cutoff"]
            )
            result["final_gate_excluded_by_upper_bound"] = (
                d_symp <= result["challenge_rejection_cutoff"]
            )
            result["threshold_rejection_proven"] = result[
                "final_gate_excluded_by_upper_bound"
            ]
            result["milp_early_stop_triggered"] = (
                effective_early_stop is not None
                and d_symp <= effective_early_stop
            )
            result["threshold_proof_lhs"] = (
                k * d_symp * d_symp * result["fom_target_denominator"]
            )
            result["threshold_proof_rhs"] = (
                result["fom_target_numerator"] * n
            )
            result["threshold_proof_distance"] = d_symp
            result["threshold_proof_source"] = "symplectic_upper_bound"
            if result["threshold_rejection_proven"]:
                result["threshold_proof_witness"] = copy.deepcopy(
                    symplectic_witness
                )
        if milp_checkpoint_path is not None:
            checkpoint = write_symplectic_weight_checkpoint(
                code,
                checkpoint_path=milp_checkpoint_path,
                checkpoint_identity=checkpoint_identity,
                witness=symplectic_witness,
                timeout_per_logical=milp_timeout_per_logical,
                total_timeout=milp_total_timeout,
                hard_timeout_per_logical=milp_hard_timeout_per_logical,
                early_stop=effective_early_stop,
                reset_incompatible_checkpoint=True,
            )
            result["milp_details"] = {
                "exact": result["d_is_exact"],
                "checkpoint_enabled": True,
                "checkpoint_path": os.path.abspath(
                    os.fspath(milp_checkpoint_path)
                ),
                "checkpoint_status": checkpoint["status"],
                "symplectic_weight_witness": copy.deepcopy(
                    symplectic_witness
                ),
            }
        return result

    # Stage 3: MILP exact distance
    result["milp_solver_attempted"] = True
    d, details = compute_distance_milp(
        code,
        timeout_per_logical=milp_timeout_per_logical,
        total_timeout=milp_total_timeout,
        early_stop=effective_early_stop,
        checkpoint_path=milp_checkpoint_path,
        resume=milp_resume,
        hard_timeout_per_logical=milp_hard_timeout_per_logical,
        checkpoint_identity=checkpoint_identity,
        # Stage 1 paths are candidate-key-bound. Source/formulation upgrades
        # must preserve the old regular file as forensic evidence and restart
        # from zero instead of making the candidate permanently un-runnable.
        reset_incompatible_checkpoint=True,
    )

    result["milp_details"] = details

    if details.get("all_timeout"):
        # A time limit with no incumbent proves neither an upper nor a lower
        # distance bound. early_stop is only a stopping policy, not a model
        # feasibility constraint.
        result["d"] = 0
        result["d_is_exact"] = False
        result["distance_trusted"] = False
        result["fom"] = 0.0
        result["fom_upper_bound"] = None
        result["exact_distance"] = None
        result["exact_fom"] = None
        result["fitness_distance_credit"] = 0.0
        result["score"] = 0.0
        result["distance_status"] = "unknown_no_incumbent"
        result["search_status"] = "retry"
        result["stage"] = "milp_timeout_no_incumbent"
    else:
        d = _positive_distance_bound(d)
        if d is None:
            return _distance_backend_retry(
                result,
                source="milp",
                value=d,
            )
        is_exact = details.get("exact") is True
        upper_fom = compute_fom(n, k, d)
        result["d"] = d
        result["d_is_exact"] = is_exact
        result["distance_trusted"] = is_exact
        result["distance_status"] = (
            "exact" if is_exact else "upper_bound"
        )
        result["distance_upper_bound"] = d
        result["distance_upper_bound_source"] = (
            "milp_exact" if is_exact else "milp_incumbent"
        )
        result["fom"] = upper_fom
        result["fom_upper_bound"] = upper_fom
        result["exact_distance"] = d if is_exact else None
        result["exact_fom"] = upper_fom if is_exact else None
        result["fitness_distance_credit"] = upper_fom if is_exact else 0.0
        result["score"] = upper_fom if is_exact else 0.0
        result["search_status"] = "exact" if is_exact else "unresolved"

        replayed_incumbent = None
        structured_witness = None
        try:
            structured_witness = _validated_feasible_threshold_witness(
                details,
                d,
            )
        except RuntimeError:
            pass
        if not is_exact:
            if structured_witness is not None:
                replayed_incumbent = _validate_replayable_css_witness(
                    code,
                    structured_witness,
                    distance=d,
                )
            result["distance_trusted"] = replayed_incumbent is not None

        if milp_target_fom is not None:
            witness_proven = is_exact or replayed_incumbent is not None
            result["fom_target_excluded_by_upper_bound"] = (
                witness_proven and d <= result["fom_rejection_cutoff"]
            )
            result["final_gate_excluded_by_upper_bound"] = (
                witness_proven and d <= result["challenge_rejection_cutoff"]
            )
            result["threshold_rejection_proven"] = bool(
                result["final_gate_excluded_by_upper_bound"]
            )
            if result["threshold_rejection_proven"]:
                result["threshold_proof_lhs"] = (
                    k * d * d * result["fom_target_denominator"]
                )
                result["threshold_proof_rhs"] = (
                    result["fom_target_numerator"] * n
                )
                result["threshold_proof_distance"] = d
                result["threshold_proof_source"] = (
                    "milp_exact"
                    if is_exact
                    else "milp_feasible_upper_bound"
                )
                if replayed_incumbent is not None:
                    result["threshold_proof_witness"] = copy.deepcopy(
                        replayed_incumbent
                    )
                elif is_exact and structured_witness is not None:
                    # Exact optimality is already sufficient for rejection;
                    # retain the solver witness as supplementary evidence.
                    result["threshold_proof_witness"] = copy.deepcopy(
                        structured_witness
                    )
                result["search_status"] = "terminal_negative"
                result["fitness_distance_credit"] = 0.0
                result["score"] = 0.0
        if effective_early_stop is not None and d <= effective_early_stop:
            if milp_target_fom is not None:
                result["milp_early_stop_triggered"] = not is_exact
            elif replayed_incumbent is not None:
                result["search_status"] = "terminal_negative"
            result["stage"] = "milp_low_d"
        elif is_exact:
            result["stage"] = "milp_exact"
        else:
            # Incumbents found but not all proven optimal -- d is an upper
            # bound on true distance, so FOM is an upper bound too.
            result["stage"] = "milp_incumbent"

    return result


def evaluate_batch_milp(
    ell: int,
    m: int,
    candidates: list[tuple[list[tuple[int, int]], list[tuple[int, int]]]],
    **kwargs,
) -> list[dict]:
    """Evaluate a batch of candidates using MILP distance.

    Args:
        ell: Cyclic group order for x.
        m: Cyclic group order for y.
        candidates: List of (A_terms, B_terms) tuples.
        **kwargs: Passed to evaluate_candidate_milp.

    Returns:
        List of result dicts, sorted by score descending.
    """
    results = []
    for candidate in candidates:
        A_terms, B_terms, geometry = _candidate_components(
            candidate, ell=ell, m=m,
        )
        result = evaluate_candidate_milp(
            ell,
            m,
            A_terms,
            B_terms,
            geometry=geometry,
            **kwargs,
        )
        results.append(result)
        if _result_ranking_score(result) > 0:
            logger.info(
                "MILP [[%d, %d, %d]] FOM=%.2f (stage=%s, %.1fs)",
                result["n"], result["k"], result["d"],
                result["fom"], result["stage"],
                result.get("milp_details", {}).get("time_s", 0),
            )
    results.sort(key=_result_ranking_score, reverse=True)
    return results


# ── Parallel k-screening ─────────────────────────────────────────


def evaluate_batch_milp_parallel(
    tasks: list[tuple[int, int, list, list]],
    *,
    max_workers: int | None = None,
    **kwargs,
) -> list[dict]:
    """Evaluate multiple candidates in parallel using ProcessPoolExecutor.

    Designed for the k-only screening phase where each candidate takes
    ~20-70ms (depending on lattice size) and there are 100k+ candidates.
    With 10 workers, this gives ~10x speedup over sequential evaluation.

    Args:
        tasks: List of (ell, m, A_terms, B_terms) tuples.
        max_workers: Number of parallel processes.  Defaults to
            min(cpu_count - 2, 10).
        **kwargs: Passed to evaluate_candidate_milp (e.g. quick=True).

    Returns:
        List of result dicts (same order as tasks).
    """
    import os
    from concurrent.futures import ProcessPoolExecutor

    if not tasks:
        return []

    if max_workers is None:
        max_workers = min((os.cpu_count() or 4) - 2, 10)
    max_workers = max(1, max_workers)

    worker_args = []
    for task in tasks:
        if len(task) == 4:
            ell, m, A, B = task
            geometry = None
        elif len(task) == 5:
            ell, m, A, B, geometry = task
        else:
            raise ValueError("MILP task must have four or five fields")
        worker_args.append((ell, m, A, B, geometry, kwargs))

    # chunksize=200 reduces IPC overhead: each worker processes 200
    # candidates per round-trip instead of 1.
    logger.info(
        "Parallel k-screening: %d tasks across %d workers",
        len(tasks), max_workers,
    )
    with ProcessPoolExecutor(max_workers=max_workers) as pool:
        results = list(pool.map(_milp_worker, worker_args, chunksize=200))

    n_valid = sum(1 for r in results if r.get("k", 0) > 0)
    logger.info(
        "Parallel k-screening done: %d/%d with k>0", n_valid, len(results),
    )
    return results


# ── Parallel MILP evaluation ─────────────────────────────────────


def _milp_worker(args):
    """Worker function for parallel evaluation (k-screening or MILP).

    Runs in a separate process via ProcessPoolExecutor.
    Args is a tuple: (ell, m, A_terms, B_terms, kwargs).
    """
    if len(args) == 5:
        ell, m, A_terms, B_terms, kwargs = args
        geometry = None
    else:
        ell, m, A_terms, B_terms, geometry, kwargs = args
    return evaluate_candidate_milp(
        ell,
        m,
        A_terms,
        B_terms,
        geometry=geometry,
        **kwargs,
    )


def _milp_cache_key(
    ell: int, m: int, A_terms, B_terms, *, geometry=None,
) -> tuple:
    """Return a strictly typed, currently valid BB candidate cache key."""
    identity = _milp_cache_candidate_identity(
        {
            "ell": ell,
            "m": m,
            "geometry": geometry,
            "A_terms": A_terms,
            "B_terms": B_terms,
        }
    )
    validate_terms(
        identity["ell"],
        identity["m"],
        identity["A_terms"],
        "A",
    )
    validate_terms(
        identity["ell"],
        identity["m"],
        identity["B_terms"],
        "B",
    )
    a = tuple(tuple(term) for term in identity["A_terms"])
    b = tuple(tuple(term) for term in identity["B_terms"])
    legacy_key = (identity["ell"], identity["m"], a, b)
    if identity["geometry"] is None:
        return legacy_key
    geometry_json = _milp_cache_json(identity["geometry"])
    return (*legacy_key, geometry_json)


def _milp_cache_json(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()


def _milp_cache_sha256(value: Any) -> str:
    return hashlib.sha256(_milp_cache_json(value)).hexdigest()


def _milp_cache_json_loads(text: str) -> Any:
    def reject_duplicate_keys(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate MILP cache key: {key!r}")
            value[key] = item
        return value

    def reject_non_finite(value):
        raise ValueError(f"non-finite MILP cache number: {value}")

    return json.loads(
        text,
        object_pairs_hook=reject_duplicate_keys,
        parse_constant=reject_non_finite,
    )


def _milp_cache_run_parameters(
    *,
    milp_timeout_per_logical: int,
    milp_total_timeout: int,
    milp_early_stop: int | None,
) -> dict[str, Any]:
    if (
        isinstance(milp_timeout_per_logical, bool)
        or not isinstance(milp_timeout_per_logical, int)
        or milp_timeout_per_logical < 1
    ):
        raise ValueError("milp_timeout_per_logical must be a positive integer")
    if (
        isinstance(milp_total_timeout, bool)
        or not isinstance(milp_total_timeout, int)
        or milp_total_timeout < 0
    ):
        raise ValueError("milp_total_timeout must be a non-negative integer")
    if (
        milp_early_stop is not None
        and (
            isinstance(milp_early_stop, bool)
            or not isinstance(milp_early_stop, int)
            or milp_early_stop < 0
        )
    ):
        raise ValueError("milp_early_stop must be a non-negative integer or None")
    return {
        "timeout_per_logical_s": milp_timeout_per_logical,
        "total_timeout_s": milp_total_timeout,
        "early_stop": milp_early_stop,
    }


def _milp_cache_implementation_fingerprint() -> dict[str, Any]:
    if _EVALUATOR_SOURCE_SHA256 is None:
        raise RuntimeError("cannot fingerprint evaluator.py for MILP cache")
    value = {
        "evaluator_py_sha256": _EVALUATOR_SOURCE_SHA256,
        "distance_milp": _distance_milp_implementation_fingerprint(),
        "cache_contract": "witness-replayed-upper-bound-v1",
    }
    value["fingerprint_sha256"] = _milp_cache_sha256(value)
    return value


def _milp_cache_candidate_identity(result: Mapping[str, Any]) -> dict[str, Any]:
    ell = result.get("ell")
    m = result.get("m")
    if (
        isinstance(ell, bool)
        or not isinstance(ell, int)
        or ell < 1
        or isinstance(m, bool)
        or not isinstance(m, int)
        or m < 1
    ):
        raise ValueError("MILP cache candidate lattice is invalid")

    def terms(name: str) -> list[list[int]]:
        raw = result.get(name)
        if not isinstance(raw, list) or not 2 <= len(raw) <= 6:
            raise ValueError(f"MILP cache candidate {name} is invalid")
        canonical: list[list[int]] = []
        for term in raw:
            if (
                not isinstance(term, (list, tuple))
                or len(term) != 2
                or any(
                    isinstance(value, bool) or not isinstance(value, int)
                    for value in term
                )
            ):
                raise ValueError(f"MILP cache candidate {name} is invalid")
            canonical.append([int(term[0]), int(term[1])])
        return sorted(canonical)

    return {
        "ell": ell,
        "m": m,
        "geometry": normalize_geometry(ell, m, result.get("geometry")),
        "A_terms": terms("A_terms"),
        "B_terms": terms("B_terms"),
    }


def _milp_cache_evidence(result: Mapping[str, Any]) -> tuple[str, dict[str, Any]]:
    symplectic = result.get("symplectic_weight_witness")
    if isinstance(symplectic, dict):
        return "symplectic_logical_witness", copy.deepcopy(symplectic)
    details = result.get("milp_details")
    if isinstance(details, Mapping):
        witness = details.get("minimum_direction_witness")
        if isinstance(witness, dict):
            return "css_direction_witness", copy.deepcopy(witness)
    raise ValueError("MILP cache result has no replayable upper-bound witness")


def _milp_cache_record(
    result: Mapping[str, Any],
    *,
    run_parameters: Mapping[str, Any],
    saved_at: float,
) -> dict[str, Any]:
    """Return a source/budget/result-bound JSONL record.

    The hash is corruption evidence, not authorization. Cache reuse separately
    rebuilds the code and replays the embedded logical witness, and never
    inherits a general exact lower-bound claim from disk.
    """
    body = copy.deepcopy(dict(result))
    body.pop("_milp_cache", None)
    body["_saved_at"] = float(saved_at)
    identity = _milp_cache_candidate_identity(body)
    evidence_kind, evidence = _milp_cache_evidence(body)
    metadata = {
        "kind": _MILP_CACHE_KIND,
        "schema_version": _MILP_CACHE_SCHEMA_VERSION,
        "implementation": _milp_cache_implementation_fingerprint(),
        "run_parameters": copy.deepcopy(dict(run_parameters)),
        "candidate_identity": identity,
        "candidate_sha256": _milp_cache_sha256(identity),
        "evidence_kind": evidence_kind,
        "evidence_sha256": _milp_cache_sha256(evidence),
        "result_sha256": _milp_cache_sha256(body),
    }
    body["_milp_cache"] = metadata
    return body


def _replay_cached_upper_bound(
    result: Mapping[str, Any],
    *,
    evidence_kind: str,
) -> tuple[int, int, int, bool, dict[str, Any]] | None:
    """Rebuild the code and replay one feasible logical upper-bound witness."""
    try:
        identity = _milp_cache_candidate_identity(result)
        validate_terms(
            identity["ell"],
            identity["m"],
            identity["A_terms"],
            "A",
        )
        validate_terms(
            identity["ell"],
            identity["m"],
            identity["B_terms"],
            "B",
        )
        code = build_bb_code(
            identity["ell"],
            identity["m"],
            identity["A_terms"],
            identity["B_terms"],
            geometry=identity["geometry"],
        )
        n, k = get_code_params_fast(code)
        distance = result.get("d")
        if (
            isinstance(distance, bool)
            or not isinstance(distance, int)
            or distance < 1
            or distance > n
            or result.get("n") != n
            or result.get("k") != k
            or k < MIN_K_THRESHOLD
        ):
            return None
        if evidence_kind == "symplectic_logical_witness":
            raw = result.get("symplectic_weight_witness")
            if not isinstance(raw, Mapping):
                return None
            replayed = symplectic_weight_witness(code, distance)
            if (
                replayed is None
                or _milp_cache_json(replayed) != _milp_cache_json(dict(raw))
            ):
                return None
            return n, k, distance, distance <= 2, replayed
        if evidence_kind != "css_direction_witness":
            return None
        details = result.get("milp_details")
        if not isinstance(details, Mapping):
            return None
        witness = details.get("minimum_direction_witness")
        if not isinstance(witness, Mapping) or set(witness) != {
            "side",
            "index",
            "weight",
            "bits",
        }:
            return None
        side = witness.get("side")
        index = witness.get("index")
        weight = witness.get("weight")
        bits = witness.get("bits")
        if (
            side not in {"X", "Z"}
            or isinstance(index, bool)
            or not isinstance(index, int)
            or index < 0
            or isinstance(weight, bool)
            or not isinstance(weight, int)
            or weight != distance
            or not isinstance(bits, list)
            or len(bits) != n
            or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
            or sum(bits) != distance
        ):
            return None
        hx, hz, lx, lz = get_code_matrices(code)
        vector = np.asarray(bits, dtype=np.uint8)
        checks, duals = (hz, lz) if side == "X" else (hx, lx)
        if index >= len(duals):
            return None
        if np.any((np.asarray(checks, dtype=np.uint8) @ vector) % 2):
            return None
        if int(np.dot(np.asarray(duals[index], dtype=np.uint8), vector) % 2) != 1:
            return None
        canonical_witness = {
            "side": side,
            "index": index,
            "weight": weight,
            "bits": list(bits),
        }
        return n, k, distance, False, canonical_witness
    except (KeyError, TypeError, ValueError, RuntimeError, ArithmeticError):
        return None


def _validated_milp_cache_result(
    raw: Any,
    *,
    implementation: Mapping[str, Any],
    run_parameters: Mapping[str, Any],
) -> dict[str, Any] | None:
    if not isinstance(raw, dict):
        return None
    metadata = raw.get("_milp_cache")
    required = {
        "kind",
        "schema_version",
        "implementation",
        "run_parameters",
        "candidate_identity",
        "candidate_sha256",
        "evidence_kind",
        "evidence_sha256",
        "result_sha256",
    }
    if not isinstance(metadata, dict) or set(metadata) != required:
        return None
    if (
        metadata.get("kind") != _MILP_CACHE_KIND
        or metadata.get("schema_version") != _MILP_CACHE_SCHEMA_VERSION
        or metadata.get("implementation") != dict(implementation)
        or metadata.get("run_parameters") != dict(run_parameters)
    ):
        return None
    try:
        body = copy.deepcopy(raw)
        body.pop("_milp_cache", None)
        identity = _milp_cache_candidate_identity(body)
        evidence_kind, evidence = _milp_cache_evidence(body)
        if (
            metadata.get("candidate_identity") != identity
            or metadata.get("candidate_sha256") != _milp_cache_sha256(identity)
            or metadata.get("evidence_kind") != evidence_kind
            or metadata.get("evidence_sha256") != _milp_cache_sha256(evidence)
            or metadata.get("result_sha256") != _milp_cache_sha256(body)
        ):
            return None
    except Exception:
        return None
    try:
        replayed = _replay_cached_upper_bound(
            body,
            evidence_kind=evidence_kind,
        )
    except Exception:
        return None
    if replayed is None:
        return None
    n, k, distance, structurally_exact, replayed_evidence = replayed
    cutoff = run_parameters.get("early_stop")
    if not structurally_exact and (cutoff is None or distance > cutoff):
        # A high-distance row needs a fresh lower-bound solve. Reusing it would
        # turn an old incumbent or unverified exact flag into permanent state.
        return None

    # Reconstruct a minimal result instead of returning the persisted body.
    # The metadata hashes are deliberately unkeyed corruption checks, so a
    # writer who controls the JSONL file could recompute them. Only fields
    # independently rebuilt or witness-replayed here may cross the boundary.
    upper_fom = compute_fom(n, k, distance)
    result = {
        **copy.deepcopy(identity),
        "n": n,
        "k": k,
        "d": distance,
        "d_is_exact": structurally_exact,
        "distance_trusted": True,
        "distance_status": "exact" if structurally_exact else "upper_bound",
        "distance_upper_bound": distance,
        "distance_upper_bound_source": (
            "milp_cache_structural_exact"
            if structurally_exact
            else "milp_cache_witness"
        ),
        "fom": upper_fom,
        "fom_upper_bound": upper_fom,
        "exact_distance": distance if structurally_exact else None,
        "exact_fom": upper_fom if structurally_exact else None,
        "fitness_distance_credit": upper_fom if structurally_exact else 0.0,
        "encoding_rate": k / n,
        "milp_effective_early_stop": cutoff,
        "milp_solver_attempted": False,
        "milp_cache_replayed": True,
        "search_status": "exact" if structurally_exact else "terminal_negative",
        "stage": (
            "milp_cache_structural_d2"
            if structurally_exact
            else "milp_cache_witness_upper_bound"
        ),
    }
    if result.get("geometry") is None:
        # Preserve the historical public result shape.  The cache identity
        # carries a canonical null internally so missing geometry and explicit
        # q=0 alias safely, but a replayed legacy result must look exactly like
        # a fresh legacy/q=0 evaluation and omit the optional field.
        result.pop("geometry", None)
    result["score"] = upper_fom if structurally_exact else 0.0
    if evidence_kind == "symplectic_logical_witness":
        result["d_symplectic"] = distance
        result["symplectic_weight_witness"] = copy.deepcopy(
            replayed_evidence
        )
    else:
        result["milp_details"] = {
            "exact": False,
            "cache_replayed": True,
            "minimum_direction_witness": copy.deepcopy(
                replayed_evidence
            ),
        }
    return result


def _open_milp_cache_stream(path: Path):
    """Open one unchanged regular cache file without following its last link."""
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    descriptor = os.open(path, flags)
    try:
        opened = os.fstat(descriptor)
        current = os.stat(path, follow_symlinks=False)
        if (
            not stat.S_ISREG(opened.st_mode)
            or not stat.S_ISREG(current.st_mode)
            or (opened.st_dev, opened.st_ino)
            != (current.st_dev, current.st_ino)
        ):
            raise OSError(f"MILP cache is not one fixed regular file: {path}")
        stream = os.fdopen(descriptor, "rb")
        descriptor = -1
        return stream
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _bounded_milp_cache_lines(stream):
    """Yield independent JSONL records without allocating an unbounded line."""
    limit = _MILP_CACHE_MAX_RECORD_BYTES
    while True:
        line = stream.readline(limit + 1)
        if not line:
            return
        if len(line) > limit:
            while line and not line.endswith(b"\n"):
                line = stream.readline(limit + 1)
            continue
        yield line


def _append_milp_cache_record(path: Path, encoded: str) -> None:
    """Append one complete record to a fixed regular file without link follow."""
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_APPEND
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    descriptor = os.open(path, flags, 0o600)
    try:
        opened = os.fstat(descriptor)
        current = os.stat(path, follow_symlinks=False)
        if (
            not stat.S_ISREG(opened.st_mode)
            or not stat.S_ISREG(current.st_mode)
            or (opened.st_dev, opened.st_ino)
            != (current.st_dev, current.st_ino)
        ):
            raise OSError(f"MILP cache is not one fixed regular file: {path}")
        payload = ("\n" + encoded + "\n").encode("utf-8")
        written = os.write(descriptor, payload)
        if written != len(payload):
            raise OSError(
                f"short MILP cache append: wrote {written}/{len(payload)} bytes"
            )
    finally:
        os.close(descriptor)


def _load_milp_cache(
    path: str | None,
    *,
    milp_timeout_per_logical: int,
    milp_total_timeout: int,
    milp_early_stop: int | None,
    requested_keys: set[tuple],
) -> dict[tuple, dict]:
    """Load only current, bound records with independently replayed witnesses."""

    cache: dict[tuple, dict] = {}
    if not path:
        return cache
    if not requested_keys:
        return cache
    run_parameters = _milp_cache_run_parameters(
        milp_timeout_per_logical=milp_timeout_per_logical,
        milp_total_timeout=milp_total_timeout,
        milp_early_stop=milp_early_stop,
    )
    p = Path(path)
    try:
        metadata = p.lstat()
    except FileNotFoundError:
        return cache
    except OSError as e:
        logger.warning("MILP cache inspect error: %s", e)
        return cache
    if not stat.S_ISREG(metadata.st_mode):
        logger.warning("MILP cache is not a regular file: %s", p)
        return cache
    try:
        implementation = _milp_cache_implementation_fingerprint()
    except Exception as e:
        # The cache is only an optimization. An unreadable source fingerprint
        # must never prevent a fresh solve.
        logger.warning("MILP cache fingerprint unavailable: %s", e)
        return cache
    try:
        with _open_milp_cache_stream(p) as stream:
            for raw_line in _bounded_milp_cache_lines(stream):
                if not raw_line.strip():
                    continue
                try:
                    line = raw_line.decode("utf-8")
                    raw = _milp_cache_json_loads(line)
                    if not isinstance(raw, Mapping):
                        continue
                    row_key = _milp_cache_key(
                        raw.get("ell"),
                        raw.get("m"),
                        raw.get("A_terms"),
                        raw.get("B_terms"),
                        geometry=raw.get("geometry"),
                    )
                    if row_key not in requested_keys:
                        continue
                    result = _validated_milp_cache_result(
                        raw,
                        implementation=implementation,
                        run_parameters=run_parameters,
                    )
                except Exception:
                    # Treat each JSONL row as an independent cache record. One
                    # torn, hostile, or non-UTF-8 append must neither discard
                    # earlier proofs nor prevent a fresh solve.
                    continue
                if result is None:
                    continue
                key = _milp_cache_key(
                    result["ell"],
                    result["m"],
                    result["A_terms"],
                    result["B_terms"],
                    geometry=result.get("geometry"),
                )
                existing = cache.get(key)
                if existing is None or result["d"] < existing["d"]:
                    cache[key] = result
    except OSError as e:
        logger.warning("MILP cache load error: %s", e)
    return cache


def evaluate_milp_parallel(
    tasks: list[tuple[int, int, list, list]],
    *,
    milp_timeout_per_logical: int = 300,
    milp_total_timeout: int = 7200,
    milp_early_stop: int = 4,
    max_workers: int | None = None,
    save_path: str | None = None,
) -> list[dict]:
    """Evaluate multiple (ell, m, A_terms, B_terms) tasks in parallel using MILP.

    Uses ProcessPoolExecutor for true parallelism (HiGHS is single-threaded,
    so each worker gets one core).  Results are saved incrementally to
    ``save_path`` (JSONL format) as each completes -- no code loss even if
    the parent process is killed.

    Includes a disk-based cache: results from previous iterations (loaded from
    ``save_path``) are reused without re-solving.  This avoids the dominant
    bottleneck where known seed codes are MILP-verified every iteration.

    Args:
        tasks: List of (ell, m, A_terms, B_terms) tuples.
        milp_timeout_per_logical: Per-logical ILP solve timeout (seconds).
        milp_total_timeout: Total timeout per code (seconds, 0=unlimited).
        milp_early_stop: Stop when d ≤ this value.
        max_workers: Number of parallel processes.  Defaults to
            min(cpu_count - 2, 10).
        save_path: Path to JSONL file for incremental persistence.
            Each result is appended as one JSON line immediately after solving.

    Returns:
        List of result dicts for all tasks, sorted by score descending.
    """
    import json
    import os
    import time as _time
    from concurrent.futures import ProcessPoolExecutor, as_completed
    from pathlib import Path

    if not tasks:
        return []

    if max_workers is None:
        max_workers = min((os.cpu_count() or 4) - 2, 10)
    max_workers = max(1, max_workers)

    # ── Load MILP cache from previous results ──────────────────────
    run_parameters = _milp_cache_run_parameters(
        milp_timeout_per_logical=milp_timeout_per_logical,
        milp_total_timeout=milp_total_timeout,
        milp_early_stop=milp_early_stop,
    )
    normalized_tasks = []
    for task in tasks:
        if len(task) == 4:
            ell, m, A_terms, B_terms = task
            geometry = None
        elif len(task) == 5:
            ell, m, A_terms, B_terms, geometry = task
        else:
            raise ValueError("MILP task must have four or five fields")
        normalized_tasks.append((ell, m, A_terms, B_terms, geometry))

    requested_cache_keys: set[tuple] = set()
    for ell, m, A_terms, B_terms, geometry in normalized_tasks:
        try:
            requested_cache_keys.add(
                _milp_cache_key(
                    ell, m, A_terms, B_terms, geometry=geometry,
                )
            )
        except Exception:
            # Invalid or non-canonical task inputs must take the ordinary
            # evaluator path; Python's bool/int or float/int equality must
            # never let them alias a valid persisted identity.
            continue
    cache = _load_milp_cache(
        save_path,
        milp_timeout_per_logical=milp_timeout_per_logical,
        milp_total_timeout=milp_total_timeout,
        milp_early_stop=milp_early_stop,
        requested_keys=requested_cache_keys,
    )

    # Separate cached vs uncached tasks
    cached_results = []
    uncached_tasks = []
    for ell, m, A_terms, B_terms, geometry in normalized_tasks:
        try:
            key = _milp_cache_key(
                ell, m, A_terms, B_terms, geometry=geometry,
            )
        except Exception:
            key = None
        cached = cache.get(key) if key is not None else None
        if cached is not None:
            cached_results.append(cached)
        else:
            uncached_tasks.append((ell, m, A_terms, B_terms, geometry))

    if cached_results:
        logger.info(
            "MILP cache: %d/%d tasks cached, %d to solve",
            len(cached_results), len(tasks), len(uncached_tasks),
        )

    kwargs = {
        "milp_timeout_per_logical": milp_timeout_per_logical,
        "milp_total_timeout": milp_total_timeout,
        "milp_early_stop": milp_early_stop,
    }

    # Prepare worker arguments for uncached tasks only
    worker_args = [
        (ell, m, A_terms, B_terms, geometry, kwargs)
        for ell, m, A_terms, B_terms, geometry in uncached_tasks
    ]

    results = list(cached_results)
    save_file = Path(save_path) if save_path else None
    if save_file:
        save_file.parent.mkdir(parents=True, exist_ok=True)

    if not worker_args:
        logger.info(
            "MILP cache: all %d tasks cached, skipping solver",
            len(tasks),
        )
        results.sort(key=_result_ranking_score, reverse=True)
        return results

    t0 = _time.monotonic()
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(_milp_worker, args): i
            for i, args in enumerate(worker_args)
        }

        for future in as_completed(futures):
            idx = futures[future]
            try:
                result = future.result()
            except Exception as e:
                ell, m, A_terms, B_terms, geometry, _ = worker_args[idx]
                logger.error(
                    "MILP worker error for (%d,%d) A=%s: %s",
                    ell, m, A_terms, e,
                )
                result = {
                    "ell": ell, "m": m,
                    "A_terms": A_terms, "B_terms": B_terms,
                    "n": 2 * ell * m, "k": 0, "d": 0,
                    "d_is_exact": False, "fom": 0.0,
                    "score": float("-inf"),
                    "stage": "worker_error",
                    "error": str(e),
                }
                canonical_geometry = normalize_geometry(ell, m, geometry)
                if canonical_geometry is not None:
                    result["geometry"] = canonical_geometry

            results.append(result)

            # Incremental save: append to JSONL immediately
            if save_file and result.get("d", 0) > 0:
                try:
                    try:
                        persisted = _milp_cache_record(
                            result,
                            run_parameters=run_parameters,
                            saved_at=_time.time(),
                        )
                    except (TypeError, ValueError, RuntimeError, ArithmeticError):
                        # Keep the candidate history even when it has no
                        # replayable cache evidence. Such a row is deliberately
                        # ignored by future cache loads.
                        persisted = copy.deepcopy(result)
                        persisted["_saved_at"] = _time.time()
                    encoded = json.dumps(
                        persisted,
                        default=str,
                        allow_nan=False,
                    )
                    # A leading separator keeps this complete record
                    # recoverable even if a killed predecessor left a
                    # truncated final line without its newline.
                    _append_milp_cache_record(save_file, encoded)
                except (OSError, TypeError, ValueError):
                    pass  # Don't fail evaluation over persistence

            # Log progress
            d = result.get("d", 0)
            if d > 0:
                logger.info(
                    "MILP [%d/%d] [[%d,%d,%d]] FOM=%.2f (%s, %.1fs)",
                    len(results) - len(cached_results), len(uncached_tasks),
                    result["n"], result["k"], d,
                    (
                        result.get("fom")
                        or result.get("fom_upper_bound")
                        or 0
                    ),
                    result.get("stage", "?"),
                    result.get("milp_details", {}).get("time_s", 0),
                )

    elapsed = _time.monotonic() - t0
    logger.info(
        "Parallel MILP: %d new + %d cached = %d total, %d workers, %.1fs",
        len(uncached_tasks), len(cached_results), len(results),
        max_workers, elapsed,
    )

    results.sort(key=_result_ranking_score, reverse=True)
    return results
