"""Focused regression tests for versioned scalar-FOM target semantics."""

import math

import pytest

from evaluation.target_policy import (
    TARGET_MODE_GIST,
    TARGET_MODE_SCALAR,
    TARGET_MODE_SCALAR_13_INCLUSIVE,
    TARGET_MODE_SCALAR_INCLUSIVE,
    classify_target_win,
    is_inclusive_scalar_target_mode,
    minimum_target_distance,
    target_binding,
    validate_target_binding,
)


def test_fom13_inclusive_mode_accepts_only_at_or_above_exact_boundary():
    assert classify_target_win(
        100, 13, 10, TARGET_MODE_SCALAR_13_INCLUSIVE,
    ) == {
        "passed": True,
        "fom": 13.0,
        "reasons": ["fom_at_least_13"],
    }
    assert classify_target_win(
        100, 13, 9, TARGET_MODE_SCALAR_13_INCLUSIVE,
    ) == {
        "passed": False,
        "fom": 10.53,
        "reasons": [],
    }
    assert is_inclusive_scalar_target_mode(
        TARGET_MODE_SCALAR_13_INCLUSIVE,
    )
    assert is_inclusive_scalar_target_mode(TARGET_MODE_SCALAR_INCLUSIVE)
    assert not is_inclusive_scalar_target_mode(TARGET_MODE_SCALAR)
    assert not is_inclusive_scalar_target_mode(TARGET_MODE_GIST)


def test_fom13_inclusive_minimum_distance_matches_integer_definition():
    for n in range(1, 50):
        for k in range(1, 25):
            required = minimum_target_distance(
                n, k, TARGET_MODE_SCALAR_13_INCLUSIVE,
            )
            assert k * required * required >= 13 * n
            assert k * (required - 1) * (required - 1) < 13 * n
            assert required == math.isqrt((13 * n - 1) // k) + 1


def test_fom13_binding_is_versioned_and_self_hashed():
    binding = target_binding(210, 10, TARGET_MODE_SCALAR_13_INCLUSIVE)
    assert binding == {
        "schema_version": 1,
        "mode": "scalar-fom-13-inclusive-v1",
        "n": 210,
        "k": 10,
        "fom_numerator": 13,
        "fom_denominator": 1,
        "strict": False,
        "required_distance": 17,
        "rejection_cutoff": 16,
        "binding_sha256": (
            "d01290b0f48ba9b888063e9c48af45946e6fa4989b4bc55ec353e467bdc890fd"
        ),
    }
    assert validate_target_binding(
        binding, 210, 10, TARGET_MODE_SCALAR_13_INCLUSIVE,
    ) == binding
    assert not classify_target_win(
        210, 10, 16, TARGET_MODE_SCALAR_13_INCLUSIVE,
    )["passed"]
    assert classify_target_win(
        210, 10, 17, TARGET_MODE_SCALAR_13_INCLUSIVE,
    )["passed"]


def test_legacy_gist_binding_bytes_remain_unchanged():
    assert target_binding(144, 12, TARGET_MODE_GIST) == {
        "schema_version": 1,
        "mode": "gist-pareto-challenge-v1",
        "n": 144,
        "k": 12,
        "fom_numerator": 12,
        "fom_denominator": 1,
        "strict": True,
        "required_distance": 13,
        "rejection_cutoff": 12,
        "binding_sha256": (
            "1175d104111ec090a6ba1712c42afffec8d8c2f7e9284290f3bbcf691b90cfef"
        ),
    }


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
