from __future__ import annotations

import numpy as np
import pytest
from qldpc.codes import BBCode
from sympy.abc import x, y

from evaluation.bb_code import (
    TwistedBBCode,
    _translation_matrix,
    build_bb_code,
    get_code_params_fast,
)
from evaluation.geometry import (
    candidate_geometry,
    geometry_basis,
    geometry_identity,
    normalize_geometry,
    reduce_coordinate,
)


TWIST_Q6 = {
    "schema_version": 1,
    "family": "twisted_torus",
    "twist": 6,
}


def test_legacy_and_zero_twist_use_exact_qldpc_path():
    a_terms = [(0, 0), (1, 0), (0, 1)]
    b_terms = [(0, 0), (2, 0), (0, 2)]
    legacy = build_bb_code(3, 4, a_terms, b_terms)
    explicit_zero = build_bb_code(
        3,
        4,
        a_terms,
        b_terms,
        geometry={
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 0,
        },
    )

    assert isinstance(legacy, BBCode)
    assert isinstance(explicit_zero, BBCode)
    assert np.array_equal(legacy.matrix_x, explicit_zero.matrix_x)
    assert np.array_equal(legacy.matrix_z, explicit_zero.matrix_z)


@pytest.mark.parametrize(
    ("exponents", "monomial"),
    [((1, 0), x), ((0, 1), y), ((2, 3), x**2 * y**3)],
)
def test_rectangular_translation_convention_matches_qldpc(exponents, monomial):
    code = build_bb_code(
        3,
        4,
        [(0, 0), (1, 0), (0, 1)],
        [(0, 0), (2, 0), (0, 2)],
    )
    expected = np.asarray(code.eval(monomial).lift().T, dtype=np.uint8)
    actual = _translation_matrix(3, 4, *exponents, twist=0)

    assert np.array_equal(actual, expected)


def test_twisted_translation_satisfies_quotient_relations():
    ell, m, twist = 6, 30, 6
    matrix_x = _translation_matrix(ell, m, 1, 0, twist=twist)
    matrix_y = _translation_matrix(ell, m, 0, 1, twist=twist)
    identity = np.eye(ell * m, dtype=np.uint8)

    assert np.array_equal(matrix_x @ matrix_y, matrix_y @ matrix_x)
    assert np.array_equal(np.linalg.matrix_power(matrix_y, m), identity)
    relation = (
        np.linalg.matrix_power(matrix_x, ell)
        @ np.linalg.matrix_power(matrix_y, twist)
    )
    assert np.array_equal(relation, identity)


def test_q6_paper_fixture_builds_360_12_css_code():
    # Generalized twisted-torus fixture:
    # A = x + x^2 + y^3, B = y + y^2 + x^3.
    code = build_bb_code(
        6,
        30,
        [(1, 0), (2, 0), (0, 3)],
        [(0, 1), (0, 2), (3, 0)],
        geometry=TWIST_Q6,
    )

    assert isinstance(code, TwistedBBCode)
    assert get_code_params_fast(code) == (360, 12)
    hx = np.asarray(code.matrix_x, dtype=np.uint8)
    hz = np.asarray(code.matrix_z, dtype=np.uint8)
    assert not np.any((hx @ hz.T) & 1)
    assert code.geometry == TWIST_Q6
    assert code.geometry_identity == {
        **TWIST_Q6,
        "ell": 6,
        "m": 30,
    }


def test_q6_fixture_is_rejected_as_known_bravyi_reencoding():
    # Expanding the outer representation must not turn a coordinate change of
    # a registered code into a false novelty claim.
    from evaluation.structural_dedup import check_css_structural_novelty

    novelty = check_css_structural_novelty(
        6,
        30,
        [(1, 0), (2, 0), (0, 3)],
        [(0, 1), (0, 2), (3, 0)],
        geometry=TWIST_Q6,
    )

    assert novelty["novel"] is False
    assert novelty["matched_reference"] == "Bravyi [[360,12,<=24]]"
    assert novelty["canonical_digest"] == novelty["reference_digest"]
    assert novelty["explicit_isomorphism"]["verified"] is True


def test_geometry_helpers_canonicalize_legacy_and_preserve_twist_identity():
    assert normalize_geometry(6, 30, None) is None
    assert normalize_geometry(
        6,
        30,
        {"schema_version": 1, "family": "rectangular"},
    ) is None
    assert normalize_geometry(
        6,
        30,
        {"schema_version": 1, "family": "twisted_torus", "twist": 0},
    ) is None
    assert candidate_geometry(
        {"ell": 6, "m": 30, "geometry": TWIST_Q6}
    ) == TWIST_Q6
    assert geometry_identity(6, 30) == {
        "schema_version": 1,
        "family": "rectangular",
        "ell": 6,
        "m": 30,
    }
    assert geometry_identity(6, 30, TWIST_Q6) != geometry_identity(6, 30)
    assert geometry_basis(6, 30, TWIST_Q6) == ((0, 30), (6, 6))


def test_coordinate_reduction_implements_x_wrap_twist_and_group_inverse():
    assert reduce_coordinate(6, 30, 6, 0, TWIST_Q6) == (0, 24)
    assert reduce_coordinate(6, 30, 6, 6, TWIST_Q6) == (0, 0)
    point = (4, 17)
    inverse = reduce_coordinate(6, 30, -point[0], -point[1], TWIST_Q6)
    assert reduce_coordinate(
        6,
        30,
        point[0] + inverse[0],
        point[1] + inverse[1],
        TWIST_Q6,
    ) == (0, 0)


@pytest.mark.parametrize(
    "geometry",
    [
        {"family": "twisted_torus", "twist": 1},
        {"schema_version": 2, "family": "twisted_torus", "twist": 1},
        {"schema_version": 1, "family": "twisted_torus", "twist": -1},
        {"schema_version": 1, "family": "twisted_torus", "twist": 30},
        {"schema_version": 1, "family": "twisted_torus", "twist": True},
        {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 1,
            "twits": 2,
        },
    ],
)
def test_geometry_validation_fails_closed(geometry):
    with pytest.raises(ValueError):
        normalize_geometry(6, 30, geometry)
