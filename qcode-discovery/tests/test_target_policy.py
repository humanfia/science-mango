"""Focused regression tests for versioned scalar-FOM target semantics."""

import math

import pytest

from evaluation.target_policy import (
    TARGET_MODE_SCALAR,
    TARGET_MODE_SCALAR_INCLUSIVE,
    classify_target_win,
    minimum_target_distance,
    target_binding,
    validate_target_binding,
)


def test_inclusive_mode_accepts_but_strict_mode_rejects_fom_12_boundary():
    assert classify_target_win(
        144, 12, 12, TARGET_MODE_SCALAR_INCLUSIVE,
    ) == {
        "passed": True,
        "fom": 12.0,
        "reasons": ["fom_at_least_12"],
    }
    assert classify_target_win(144, 12, 12, TARGET_MODE_SCALAR) == {
        "passed": False,
        "fom": 12.0,
        "reasons": [],
    }


def test_inclusive_distance_and_rejection_cutoff_are_exact_at_boundary():
    binding = target_binding(144, 12, TARGET_MODE_SCALAR_INCLUSIVE)

    assert binding == {
        "schema_version": 1,
        "mode": "scalar-fom-inclusive-v1",
        "n": 144,
        "k": 12,
        "fom_numerator": 12,
        "fom_denominator": 1,
        "strict": False,
        "required_distance": 12,
        "rejection_cutoff": 11,
        "binding_sha256": (
            "498c4b272928481dfb64ec33dc70410dd77845f085ad0a64d2781c01a2f00e60"
        ),
    }
    assert validate_target_binding(
        binding, 144, 12, TARGET_MODE_SCALAR_INCLUSIVE,
    ) == binding


def test_inclusive_minimum_distance_matches_integer_definition():
    for n in range(1, 50):
        for k in range(1, 25):
            required = minimum_target_distance(
                n, k, TARGET_MODE_SCALAR_INCLUSIVE,
            )
            assert k * required * required >= 12 * n
            assert k * (required - 1) * (required - 1) < 12 * n
            assert required == math.isqrt((12 * n - 1) // k) + 1


def test_strict_binding_bytes_remain_unchanged():
    assert target_binding(144, 12, TARGET_MODE_SCALAR) == {
        "schema_version": 1,
        "mode": "scalar-fom-strict-v1",
        "n": 144,
        "k": 12,
        "fom_numerator": 12,
        "fom_denominator": 1,
        "strict": True,
        "required_distance": 13,
        "rejection_cutoff": 12,
        "binding_sha256": (
            "d0dbdff9240e55f78d839b81e188ee708dbecbff4d2d560c95f6576c23fdffee"
        ),
    }


def test_inclusive_binding_fails_closed_if_strict_flag_is_forged():
    binding = target_binding(144, 12, TARGET_MODE_SCALAR_INCLUSIVE)
    binding["strict"] = True

    with pytest.raises(ValueError, match="SHA-256 mismatch"):
        validate_target_binding(binding, 144, 12)
