import numpy as np
import pytest

from evaluation.matrix_io import (
    build_css_from_matrices,
    build_noncss_from_matrix,
    css_parameters,
    pack_matrix,
    parse_binary_matrix,
)


def test_matrix_round_trip_and_generic_css():
    hx = np.array([[1, 1, 0, 0], [0, 0, 1, 1]], dtype=np.uint8)
    hz = np.array([[1, 1, 1, 1]], dtype=np.uint8)
    code, rebuilt_x, rebuilt_z = build_css_from_matrices(pack_matrix(hx), ["1111"])
    assert np.array_equal(rebuilt_x, hx)
    assert np.array_equal(rebuilt_z, hz)
    assert css_parameters(rebuilt_x, rebuilt_z) == (4, 1)
    assert code.num_qudits == 4
    assert code.dimension == 1


def test_matrix_input_rejects_nonbinary_and_noncommuting():
    with pytest.raises(ValueError, match="binary"):
        parse_binary_matrix([[0, 2]], name="H")
    with pytest.raises(ValueError, match="do not commute"):
        build_css_from_matrices([[1, 0]], [[1, 0]])


def test_noncss_input_checks_symplectic_commutation():
    code, stabilizer = build_noncss_from_matrix([[1, 0, 0, 1]])
    assert stabilizer.shape == (1, 4)
    assert code.num_qudits == 2
    with pytest.raises(ValueError, match="do not commute"):
        build_noncss_from_matrix([[1, 0, 0, 0], [0, 0, 1, 0]])
