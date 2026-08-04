import json

import pytest

from evaluation.algebraic_mechanisms import (
    RELATION_TYPES,
    classify_algebraic_mechanism,
)
from evaluation.geometry import reduce_coordinate


TWIST_Q2 = {
    "schema_version": 1,
    "family": "twisted_torus",
    "twist": 2,
}


def test_affine_orbit_accepts_candidate_mapping_and_is_order_stable():
    candidate = {
        "ell": 12,
        "m": 12,
        "A_terms": [[0, 0], [1, 0], [0, 2]],
        "B_terms": [[4, 3], [5, 3], [4, 5]],
    }
    descriptor = classify_algebraic_mechanism(candidate)
    reordered = classify_algebraic_mechanism(
        {
            **candidate,
            "A_terms": list(reversed(candidate["A_terms"])),
            "B_terms": list(reversed(candidate["B_terms"])),
        }
    )

    assert descriptor == reordered
    assert descriptor["relation_type"] == "affine_orbit"
    assert descriptor["support_split_type"] == "3+3"
    assert descriptor["orbit_span_bin"] == 2


def _translate(terms, shift_x, shift_y, ell, m):
    return [
        ((x + shift_x) % ell, (y + shift_y) % m)
        for x, y in terms
    ]


@pytest.mark.parametrize(
    ("ell", "m", "a_terms", "b_terms"),
    (
        (
            6,
            8,
            [(5, 7), (0, 7), (5, 0)],
            [(2, 3), (3, 3), (2, 4)],
        ),
        (
            6,
            6,
            [(5, 5), (0, 0), (1, 1)],
            [(3, 5), (3, 0), (3, 1)],
        ),
        (
            12,
            6,
            [(11, 5), (0, 5), (11, 0), (2, 1)],
            [(11, 5), (0, 5), (3, 2)],
        ),
    ),
)
def test_torus_descriptor_is_invariant_under_every_common_translation(
    ell, m, a_terms, b_terms
):
    baseline = classify_algebraic_mechanism(
        a_terms, b_terms, ell=ell, m=m
    )
    for shift_x in range(ell):
        for shift_y in range(m):
            translated = classify_algebraic_mechanism(
                _translate(a_terms, shift_x, shift_y, ell, m),
                _translate(b_terms, shift_x, shift_y, ell, m),
                ell=ell,
                m=m,
            )
            assert translated == baseline


def test_explicit_q0_preserves_rectangular_descriptor():
    candidate = {
        "ell": 6,
        "m": 8,
        "A_terms": [(5, 7), (0, 7), (5, 0)],
        "B_terms": [(2, 3), (3, 3), (2, 4)],
    }
    explicit_zero = {
        **candidate,
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 0,
        },
    }

    assert classify_algebraic_mechanism(explicit_zero) == (
        classify_algebraic_mechanism(candidate)
    )


def test_twisted_descriptor_uses_quotient_translation_across_x_wrap():
    ell, m = 4, 6
    a_terms = [(3, 5), (0, 1), (2, 2)]
    b_terms = [
        reduce_coordinate(ell, m, x + 1, y, TWIST_Q2)
        for x, y in a_terms
    ]
    twisted = classify_algebraic_mechanism(
        a_terms,
        b_terms,
        ell=ell,
        m=m,
        geometry=TWIST_Q2,
    )
    rectangular = classify_algebraic_mechanism(
        a_terms, b_terms, ell=ell, m=m,
    )

    assert twisted["relation_type"] == "affine_orbit"
    assert rectangular["relation_type"] != "affine_orbit"


def test_twisted_descriptor_is_invariant_under_every_quotient_translation():
    ell, m = 4, 6
    a_terms = [(3, 5), (0, 1), (2, 2)]
    b_terms = [(0, 0), (1, 3), (3, 4)]
    baseline = classify_algebraic_mechanism({
        "ell": ell,
        "m": m,
        "geometry": TWIST_Q2,
        "A_terms": a_terms,
        "B_terms": b_terms,
    })
    for shift_x in range(ell):
        for shift_y in range(m):
            translated_a = [
                reduce_coordinate(
                    ell, m, x + shift_x, y + shift_y, TWIST_Q2,
                )
                for x, y in a_terms
            ]
            translated_b = [
                reduce_coordinate(
                    ell, m, x + shift_x, y + shift_y, TWIST_Q2,
                )
                for x, y in b_terms
            ]
            assert classify_algebraic_mechanism(
                translated_a,
                translated_b,
                ell=ell,
                m=m,
                geometry=TWIST_Q2,
            ) == baseline


def test_relation_and_geometry_bins_are_invariant_under_a_b_exchange():
    a_terms = [(0, 0), (1, 0)]
    b_terms = [(0, 0), (2, 0), (0, 1)]
    forward = classify_algebraic_mechanism(
        a_terms, b_terms, ell=12, m=6
    )
    exchanged = classify_algebraic_mechanism(
        b_terms, a_terms, ell=12, m=6
    )

    for field in (
        "relation_type",
        "orbit_span_bin",
        "difference_spectrum_bin",
    ):
        assert exchanged[field] == forward[field]
    assert forward["support_split_type"] == "2+3"
    assert exchanged["support_split_type"] == "3+2"


def test_orbit_span_requires_one_observed_cyclic_direction():
    descriptor = classify_algebraic_mechanism(
        [(0, 0), (1, 0), (0, 2)],
        [(4, 3), (5, 3), (4, 5)],
        ell=11,
        m=13,
    )

    # Although Z_11 x Z_13 is abstractly cyclic, neither observed axis
    # difference generates an orbit containing the other.  The descriptor is
    # a local support-orbit heuristic, not abstract group generator rank.
    assert descriptor["orbit_span_bin"] == 2

    wrapped_diagonal = classify_algebraic_mechanism(
        [(11, 11), (0, 0), (1, 1)],
        [(4, 4), (5, 5)],
        ell=12,
        m=12,
    )
    assert wrapped_diagonal["orbit_span_bin"] == 1


def test_complementary_diagonal_precedes_generic_affine_equivalence():
    descriptor = classify_algebraic_mechanism(
        [(0, 0), (1, 1), (2, 2)],
        [(4, 4), (5, 3), (6, 2)],
    )
    assert descriptor["relation_type"] == "complementary_diagonal"
    assert descriptor["difference_spectrum_bin"] == 1


def test_shared_anchor_coset_detects_common_anchor_and_direction():
    descriptor = classify_algebraic_mechanism(
        [(0, 0), (1, 0), (2, 0), (0, 1)],
        [(0, 0), (1, 0), (3, 1)],
    )
    assert descriptor["relation_type"] == "shared_anchor_coset"
    assert descriptor["support_split_type"] == "4+3"


def test_asymmetric_anchor_detects_rank_imbalance():
    descriptor = classify_algebraic_mechanism(
        [(0, 0), (1, 0), (0, 1)],
        [(5, 5), (6, 5)],
    )
    assert descriptor["relation_type"] == "asymmetric_anchor"


def test_unstructured_fallback_and_json_serialisation():
    descriptor = classify_algebraic_mechanism(
        [(0, 0), (1, 0), (0, 2)],
        [(4, 3), (6, 3), (5, 6), (8, 8)],
    )
    assert descriptor["relation_type"] == "unstructured"
    assert descriptor["relation_type"] in RELATION_TYPES
    assert json.loads(json.dumps(descriptor, sort_keys=True)) == descriptor


def test_generic_term_forms_and_sparse_polynomial_mapping():
    descriptor = classify_algebraic_mechanism(
        (
            [{"x": 0, "y": 0}, {"x_exp": 1, "y_exp": 1}],
            {(0, 0): 1, (1, -1): True, (9, 9): 0},
        )
    )
    assert descriptor["relation_type"] == "complementary_diagonal"
    assert descriptor["support_split_type"] == "2+2"


def test_torus_normalisation_is_deterministic_and_deduplicates_terms():
    descriptor = classify_algebraic_mechanism(
        {
            "ell": 5,
            "m": 7,
            "A_terms": [(0, 0), (5, 7), (1, 0)],
            "B_terms": [(2, 2), (3, 2)],
        }
    )
    assert descriptor["support_split_type"] == "2+2"
    assert descriptor["relation_type"] == "affine_orbit"


@pytest.mark.parametrize(
    "candidate",
    (
        {"A_terms": [(0, 0)]},
        {"A_terms": [(0, 0)], "B_terms": [(0, 0)], "ell": 0},
        {"A_terms": [(0, 0, 1)], "B_terms": [(0, 0)]},
    ),
)
def test_invalid_candidates_fail_explicitly(candidate):
    with pytest.raises((TypeError, ValueError)):
        classify_algebraic_mechanism(candidate)
