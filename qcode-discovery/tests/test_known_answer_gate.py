"""Unit tests for deterministic helpers in the known-answer gate."""

import numpy as np

from tests.verify_known_answer_gate import connected_tanner_graph, matrix_sha256, rank_f2


def test_rank_f2():
    matrix = np.array([[1, 0, 1, 1], [0, 1, 1, 0], [1, 1, 0, 1]],
                      dtype=np.uint8)
    assert rank_f2(matrix) == 2


def test_matrix_hash_includes_shape_and_content():
    a = np.array([[1, 0], [0, 1]], dtype=np.uint8)
    b = np.array([[1, 0, 0, 1]], dtype=np.uint8)
    assert matrix_sha256(a) == matrix_sha256(a.copy())
    assert matrix_sha256(a) != matrix_sha256(b)


def test_connected_tanner_graph():
    connected = np.array([[1, 1, 0], [0, 1, 1]], dtype=np.uint8)
    disconnected = np.array([[1, 0], [0, 1]], dtype=np.uint8)
    assert connected_tanner_graph(connected) == (True, 1)
    assert connected_tanner_graph(disconnected) == (False, 2)
