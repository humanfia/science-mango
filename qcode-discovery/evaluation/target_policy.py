"""Canonical target policies for qLDPC search and certification.

The target descriptor is a small self-hashed contract.  Producers may carry
it through untrusted pipeline records, while certificate builders and
verifiers always recompute every derived field from the rebuilt ``n`` and
``k`` parameters.
"""

from __future__ import annotations

import hashlib
import json
import math
from typing import Any, Mapping


TARGET_POLICY_SCHEMA_VERSION = 1
TARGET_MODE_SCALAR = "scalar-fom-strict-v1"
TARGET_MODE_SCALAR_INCLUSIVE = "scalar-fom-inclusive-v1"
TARGET_MODE_SCALAR_13_INCLUSIVE = "scalar-fom-13-inclusive-v1"
TARGET_MODE_GIST = "gist-pareto-challenge-v1"
DEFAULT_TARGET_MODE = TARGET_MODE_GIST

FOM_NUMERATOR = 12
FOM_DENOMINATOR = 1
FOM_THRESHOLD = FOM_NUMERATOR / FOM_DENOMINATOR
_SCALAR_TARGET_POLICIES: dict[str, tuple[int, int, bool, str]] = {
    TARGET_MODE_SCALAR: (
        FOM_NUMERATOR, FOM_DENOMINATOR, False, "fom_strictly_above_12",
    ),
    TARGET_MODE_SCALAR_INCLUSIVE: (
        FOM_NUMERATOR, FOM_DENOMINATOR, True, "fom_at_least_12",
    ),
    TARGET_MODE_SCALAR_13_INCLUSIVE: (13, 1, True, "fom_at_least_13"),
}
SUPPORTED_TARGET_MODES = frozenset(
    {TARGET_MODE_GIST, *_SCALAR_TARGET_POLICIES}
)
KNOWN_PARETO_REFERENCES = (
    (72, 12, 6),
    (90, 8, 10),
    (108, 8, 10),
    (144, 12, 12),
    (288, 12, 18),
)


def _canonical_sha256(value: Mapping[str, Any]) -> str:
    encoded = json.dumps(
        dict(value),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _positive_int(name: str, value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{name} must be a positive integer")
    return value


def _distance_int(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError("d must be a non-negative integer")
    return value


def validate_target_mode(mode: Any) -> str:
    """Return one supported target mode or reject an untrusted value."""

    if not isinstance(mode, str) or mode not in SUPPORTED_TARGET_MODES:
        supported = ", ".join(sorted(SUPPORTED_TARGET_MODES))
        raise ValueError(
            f"unsupported target mode {mode!r}; expected one of {supported}"
        )
    return mode


def is_inclusive_scalar_target_mode(mode: Any) -> bool:
    """Return whether ``mode`` is a supported inclusive scalar policy."""

    selected = validate_target_mode(mode)
    policy = _SCALAR_TARGET_POLICIES.get(selected)
    return policy is not None and policy[2]


def _classify_gist_win(n: int, k: int, d: int) -> dict[str, Any]:
    """Implement the historical challenge gist exactly."""

    fom = k * d * d / n if n > 0 else 0.0
    reasons: list[str] = []
    if fom > FOM_THRESHOLD:
        reasons.append("fom_strictly_above_12")
    for ref_n, ref_k, ref_d in KNOWN_PARETO_REFERENCES:
        ref_fom = ref_k * ref_d * ref_d / ref_n
        label = f"[[{ref_n},{ref_k},{ref_d}]]"
        if math.isclose(fom, ref_fom, rel_tol=0.0, abs_tol=1e-12) and n < ref_n:
            reasons.append(f"same_fom_smaller_n_than_{label}")
        if n == ref_n and d == ref_d and k > ref_k:
            reasons.append(f"higher_k_than_{label}_with_n_d_fixed")
        if n == ref_n and k == ref_k and d > ref_d:
            reasons.append(f"higher_d_than_{label}_with_n_k_fixed")
    return {"passed": bool(reasons), "fom": fom, "reasons": reasons}


def classify_target_win(
    n: int,
    k: int,
    d: int,
    mode: str = DEFAULT_TARGET_MODE,
) -> dict[str, Any]:
    """Classify one distance under an explicit target policy.

    Scalar decisions deliberately use integer comparisons under the selected
    versioned policy. The floating-point FOM is reporting metadata only and
    cannot change a boundary decision.
    """

    n = _positive_int("n", n)
    k = _positive_int("k", k)
    d = _distance_int(d)
    mode = validate_target_mode(mode)
    if mode == TARGET_MODE_GIST:
        return _classify_gist_win(n, k, d)

    numerator, denominator, inclusive, reason = _SCALAR_TARGET_POLICIES[mode]
    lhs = k * d * d * denominator
    rhs = numerator * n
    passed = lhs >= rhs if inclusive else lhs > rhs
    return {
        "passed": passed,
        "fom": k * d * d / n,
        "reasons": [reason] if passed else [],
    }


def minimum_target_distance(
    n: int,
    k: int,
    mode: str = DEFAULT_TARGET_MODE,
) -> int:
    """Return the least integer distance satisfying the selected target.

    Unlike the legacy ``minimum_winning_distance`` helper, this contract also
    represents targets that are unattainable at a given block length.  Thus a
    returned distance may be greater than ``n``; this is useful for a complete
    rejection cutoff and lets small negative certificates remain target-bound.
    """

    n = _positive_int("n", n)
    k = _positive_int("k", k)
    mode = validate_target_mode(mode)
    if mode != TARGET_MODE_GIST:
        numerator, denominator, inclusive, _reason = (
            _SCALAR_TARGET_POLICIES[mode]
        )
        # Equality loses for a strict target and wins for an inclusive target.
        # Subtract one only in the latter case before deriving the exact
        # integer squared cutoff.
        losing_numerator = numerator * n - (1 if inclusive else 0)
        cutoff_squared = losing_numerator // (denominator * k)
        return math.isqrt(cutoff_squared) + 1
    scalar_cutoff_squared = (FOM_NUMERATOR * n) // (FOM_DENOMINATOR * k)
    scalar_required = math.isqrt(scalar_cutoff_squared) + 1
    for distance in range(1, scalar_required + 1):
        if _classify_gist_win(n, k, distance)["passed"]:
            return distance
    raise AssertionError("the gist target must include the scalar target")


def target_binding(
    n: int,
    k: int,
    mode: str = DEFAULT_TARGET_MODE,
) -> dict[str, Any]:
    """Build the canonical, self-hashed descriptor for one target."""

    n = _positive_int("n", n)
    k = _positive_int("k", k)
    mode = validate_target_mode(mode)
    required_distance = minimum_target_distance(n, k, mode)
    if mode == TARGET_MODE_GIST:
        numerator, denominator, strict = FOM_NUMERATOR, FOM_DENOMINATOR, True
    else:
        numerator, denominator, inclusive, _reason = (
            _SCALAR_TARGET_POLICIES[mode]
        )
        strict = not inclusive
    binding: dict[str, Any] = {
        "schema_version": TARGET_POLICY_SCHEMA_VERSION,
        "mode": mode,
        "n": n,
        "k": k,
        "fom_numerator": numerator,
        "fom_denominator": denominator,
        "strict": strict,
        "required_distance": required_distance,
        "rejection_cutoff": required_distance - 1,
    }
    binding["binding_sha256"] = _canonical_sha256(binding)
    return binding


def validate_target_binding(
    binding: Any,
    n: int,
    k: int,
    mode: str | None = None,
) -> dict[str, Any]:
    """Validate and normalize an untrusted target descriptor.

    ``target_mode`` is accepted as an input alias for early pipeline records;
    the returned descriptor always uses the canonical ``mode`` field.
    """

    n = _positive_int("n", n)
    k = _positive_int("k", k)
    if not isinstance(binding, Mapping):
        raise ValueError("target binding must be an object")
    supplied = dict(binding)
    stored_sha256 = supplied.pop("binding_sha256", None)
    try:
        actual_sha256 = _canonical_sha256(supplied)
    except (TypeError, ValueError) as exc:
        raise ValueError("target binding is not canonical JSON") from exc
    if not isinstance(stored_sha256, str) or stored_sha256 != actual_sha256:
        raise ValueError("target binding SHA-256 mismatch")

    descriptor_mode = supplied.get("mode")
    alias_mode = supplied.get("target_mode")
    if descriptor_mode is None:
        descriptor_mode = alias_mode
    elif alias_mode is not None and alias_mode != descriptor_mode:
        raise ValueError("target mode aliases disagree")
    descriptor_mode = validate_target_mode(descriptor_mode)
    if mode is not None and descriptor_mode != validate_target_mode(mode):
        raise ValueError("target binding mode does not match the requested mode")

    normalized = dict(supplied)
    normalized.pop("target_mode", None)
    normalized["mode"] = descriptor_mode
    expected = target_binding(n, k, descriptor_mode)
    expected_unsigned = dict(expected)
    expected_unsigned.pop("binding_sha256")
    if normalized != expected_unsigned:
        raise ValueError("target binding does not match recomputed parameters")
    return expected


__all__ = [
    "DEFAULT_TARGET_MODE",
    "FOM_DENOMINATOR",
    "FOM_NUMERATOR",
    "FOM_THRESHOLD",
    "KNOWN_PARETO_REFERENCES",
    "SUPPORTED_TARGET_MODES",
    "TARGET_MODE_GIST",
    "TARGET_MODE_SCALAR",
    "TARGET_MODE_SCALAR_13_INCLUSIVE",
    "TARGET_MODE_SCALAR_INCLUSIVE",
    "TARGET_POLICY_SCHEMA_VERSION",
    "classify_target_win",
    "is_inclusive_scalar_target_mode",
    "minimum_target_distance",
    "target_binding",
    "validate_target_binding",
    "validate_target_mode",
]
