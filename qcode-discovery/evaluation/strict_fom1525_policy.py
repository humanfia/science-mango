"""Canonical strict-15.25 target policy used by the W6 source-bound lane.

The binding bytes intentionally reproduce the descriptor emitted by
``scripts/screen_one_fom1525_w6_xor_negative.py``.  In particular, the
human-readable integer predicate is part of the self-hashed contract.
Hardware admissibility remains a separate, explicit CSS-W6 requirement and
is not added to the historical target bytes.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections.abc import Mapping
from typing import Any

from evaluation.admissibility_policy import (
    CSS_W6_ADMISSIBILITY_MODE,
    css_w6_admissibility_binding,
)


TARGET_SCHEMA_VERSION = 1
TARGET_MODE = "scalar-fom-61-over-4-strict-v1"
FOM_NUMERATOR = 61
FOM_DENOMINATOR = 4
INTEGER_PREDICATE = "4*k*d^2 > 61*n"
WIN_REASON = "fom_strictly_above_61_over_4"
REQUIRES_CSS_W6_ADMISSIBILITY = True


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _positive_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return value


def _distance_int(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError("d must be a non-negative integer")
    return value


def minimum_target_distance(n: int, k: int) -> int:
    """Return the least integer ``d`` satisfying ``4*k*d^2 > 61*n``."""

    n = _positive_int(n, "n")
    k = _positive_int(k, "k")
    cutoff_squared = (FOM_NUMERATOR * n) // (FOM_DENOMINATOR * k)
    return math.isqrt(cutoff_squared) + 1


def build_target_binding(n: int, k: int) -> dict[str, Any]:
    """Build the exact self-hashed source-runner target descriptor."""

    n = _positive_int(n, "n")
    k = _positive_int(k, "k")
    required_distance = minimum_target_distance(n, k)
    binding: dict[str, Any] = {
        "schema_version": TARGET_SCHEMA_VERSION,
        "mode": TARGET_MODE,
        "n": n,
        "k": k,
        "fom_numerator": FOM_NUMERATOR,
        "fom_denominator": FOM_DENOMINATOR,
        "strict": True,
        "required_distance": required_distance,
        "rejection_cutoff": required_distance - 1,
        "integer_predicate": INTEGER_PREDICATE,
    }
    binding["binding_sha256"] = _canonical_sha256(binding)
    return binding


def validate_target_binding(
    value: Any,
    n: int,
    k: int,
) -> dict[str, Any]:
    """Validate an untrusted descriptor against freshly recomputed bytes."""

    n = _positive_int(n, "n")
    k = _positive_int(k, "k")
    if not isinstance(value, Mapping):
        raise ValueError("strict-15.25 target binding must be a mapping")
    supplied = dict(value)
    stored_sha256 = supplied.pop("binding_sha256", None)
    try:
        actual_sha256 = _canonical_sha256(supplied)
    except (TypeError, ValueError) as exc:
        raise ValueError(
            "strict-15.25 target binding is not canonical JSON",
        ) from exc
    if stored_sha256 != actual_sha256:
        raise ValueError("strict-15.25 target binding SHA-256 mismatch")
    expected = build_target_binding(n, k)
    if dict(value) != expected:
        raise ValueError(
            "strict-15.25 target binding does not match recomputed parameters",
        )
    return expected


def classify_target(n: int, k: int, d: int) -> dict[str, Any]:
    """Classify a distance with an exact integer comparison."""

    n = _positive_int(n, "n")
    k = _positive_int(k, "k")
    d = _distance_int(d)
    lhs = FOM_DENOMINATOR * k * d * d
    rhs = FOM_NUMERATOR * n
    passed = lhs > rhs
    return {
        "passed": passed,
        "fom": k * d * d / n,
        "reasons": [WIN_REASON] if passed else [],
        "integer_predicate": INTEGER_PREDICATE,
        "integer_lhs": lhs,
        "integer_rhs": rhs,
    }


def requires_css_w6_admissibility() -> bool:
    """Return the campaign's explicit hardware-admissibility requirement."""

    return REQUIRES_CSS_W6_ADMISSIBILITY


def css_w6_requirement() -> dict[str, Any]:
    """Return the separately bound canonical CSS-W6 requirement."""

    binding = css_w6_admissibility_binding()
    return {
        "required": True,
        "code_type": "css",
        "mode": CSS_W6_ADMISSIBILITY_MODE,
        "binding_sha256": binding["binding_sha256"],
    }


# Explicit long-form aliases make imports self-documenting at integration
# points while retaining compact module-local APIs.
build_strict_fom1525_target = build_target_binding
validate_strict_fom1525_target = validate_target_binding
classify_strict_fom1525 = classify_target
minimum_strict_fom1525_distance = minimum_target_distance


__all__ = [
    "FOM_DENOMINATOR",
    "FOM_NUMERATOR",
    "INTEGER_PREDICATE",
    "REQUIRES_CSS_W6_ADMISSIBILITY",
    "TARGET_MODE",
    "TARGET_SCHEMA_VERSION",
    "WIN_REASON",
    "build_strict_fom1525_target",
    "build_target_binding",
    "classify_strict_fom1525",
    "classify_target",
    "css_w6_requirement",
    "minimum_strict_fom1525_distance",
    "minimum_target_distance",
    "requires_css_w6_admissibility",
    "validate_strict_fom1525_target",
    "validate_target_binding",
]
