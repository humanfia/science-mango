from math import gcd

import numpy as np
import pytest

from evaluation.bb_code import build_bb_code, validate_terms
from evaluation.search_sampling import (
    DEFAULT_SPLITS,
    FRONTIER_TEMPLATES,
    sample_bb_supports,
    sample_mixed,
    sample_structured_frontier,
    sample_uniform,
)


def _assert_valid_supports(ell, m, a_terms, b_terms):
    assert a_terms
    assert b_terms
    assert len(a_terms) + len(b_terms) <= 6
    assert len(a_terms) == len(set(a_terms))
    assert len(b_terms) == len(set(b_terms))
    assert all(0 <= x < ell and 0 <= y < m for x, y in a_terms + b_terms)
    validate_terms(ell, m, a_terms, "A")
    validate_terms(ell, m, b_terms, "B")


def test_uniform_is_replayable_and_returns_metadata():
    first = sample_uniform(9, 6, rng=1234, return_metadata=True)
    second = sample_uniform(9, 6, rng=1234, return_metadata=True)
    assert first == second
    a_terms, b_terms, metadata = first
    _assert_valid_supports(9, 6, a_terms, b_terms)
    assert metadata["mode"] == "uniform"
    assert metadata["shape"] == [9, 6]
    assert metadata["split"] == [len(a_terms), len(b_terms)]
    assert metadata["total_weight"] == len(a_terms) + len(b_terms)


def test_uniform_covers_configured_weight_splits():
    rng = np.random.default_rng(91)
    observed = set()
    for _ in range(300):
        a_terms, b_terms, metadata = sample_uniform(
            6, 6, rng=rng, return_metadata=True,
        )
        _assert_valid_supports(6, 6, a_terms, b_terms)
        observed.add(tuple(metadata["split"]))
    assert observed == set(DEFAULT_SPLITS)


def test_structured_transform_preserves_weight_and_uses_target_ring_units():
    label = "pareto-144-12-12"
    template = next(item for item in FRONTIER_TEMPLATES if item.label == label)
    a_terms, b_terms, metadata = sample_structured_frontier(
        12,
        6,
        rng=2026,
        template_labels=(label,),
        max_mutations=0,
        swap_probability=0.0,
        return_metadata=True,
    )
    _assert_valid_supports(12, 6, a_terms, b_terms)
    assert len(a_terms) == len(template.a_terms)
    assert len(b_terms) == len(template.b_terms)
    assert metadata["template"]["label"] == label
    assert metadata["template"]["shape_adaptation"] == "exact"
    scaling = next(
        operation
        for operation in metadata["operations"]
        if operation["op"] == "unit-scaling"
    )
    assert gcd(scaling["unit_x"], 12) == 1
    assert gcd(scaling["unit_y"], 6) == 1


def test_structured_support_reuse_and_mutation_keep_nonempty_split():
    a_terms, b_terms, metadata = sample_structured_frontier(
        24,
        6,
        rng=7,
        template_labels=("near-frontier-144-k2",),
        max_mutations=3,
        mutation_radius=2,
        swap_probability=1.0,
        return_metadata=True,
    )
    _assert_valid_supports(24, 6, a_terms, b_terms)
    assert metadata["template"]["shape_adaptation"] == "support-reuse"
    assert metadata["template"]["split"] == [4, 2]
    assert metadata["split"] == [2, 4]
    assert metadata["swapped"] is True
    assert metadata["mutations_completed"] <= metadata["mutations_requested"]
    assert len(a_terms) + len(b_terms) == 6


def test_structured_sample_does_not_alias_template_storage():
    label = "pareto-72-12-6"
    template = next(item for item in FRONTIER_TEMPLATES if item.label == label)
    original = (template.a_terms, template.b_terms)
    a_terms, b_terms = sample_structured_frontier(
        6,
        6,
        rng=4,
        template_labels=(label,),
        max_mutations=0,
    )
    a_terms[0] = (0, 0)
    b_terms.reverse()
    assert (template.a_terms, template.b_terms) == original


@pytest.mark.parametrize(
    ("probability", "component_mode"),
    ((0.0, "uniform"), (1.0, "structured-frontier")),
)
def test_mixed_selects_requested_component_and_is_replayable(
    probability, component_mode,
):
    first = sample_mixed(
        12,
        6,
        rng=44,
        structured_probability=probability,
        return_metadata=True,
    )
    second = sample_mixed(
        12,
        6,
        rng=44,
        structured_probability=probability,
        return_metadata=True,
    )
    assert first == second
    a_terms, b_terms, metadata = first
    _assert_valid_supports(12, 6, a_terms, b_terms)
    assert metadata["mode"] == "mixed"
    assert metadata["component_mode"] == component_mode
    assert metadata["structured_probability"] == probability


def test_dispatch_and_numpy_generator_stream():
    direct_rng = np.random.default_rng(88)
    dispatch_rng = np.random.default_rng(88)
    direct = sample_uniform(6, 6, rng=direct_rng, return_metadata=True)
    dispatched = sample_bb_supports(
        "uniform", 6, 6, rng=dispatch_rng, return_metadata=True,
    )
    assert direct == dispatched


def test_samples_construct_with_existing_bb_shape():
    a_terms, b_terms = sample_mixed(
        9, 6, rng=19, structured_probability=0.5,
    )
    code = build_bb_code(9, 6, a_terms, b_terms)
    assert code.num_qudits == 108


def test_invalid_constraints_fail_closed():
    with pytest.raises(ValueError, match="at most six"):
        sample_uniform(6, 6, rng=1, splits=((3, 4),))
    with pytest.raises(ValueError, match="compatible"):
        sample_structured_frontier(
            6, 6, rng=1, template_labels=("does-not-exist",),
        )
    with pytest.raises(ValueError, match="structured_probability"):
        sample_mixed(6, 6, rng=1, structured_probability=1.1)
