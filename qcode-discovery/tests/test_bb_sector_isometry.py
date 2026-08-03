from __future__ import annotations

import numpy as np

from evaluation.bb_code import build_bb_code
from evaluation.bb_sector_isometry import (
    bb_xz_inversion_block_swap_permutation,
    verify_bb_xz_sector_isometry,
)
from evaluation.distance_milp import get_code_matrices


def _matrices():
    code = build_bb_code(
        3,
        4,
        [(0, 0), (1, 0), (0, 1)],
        [(0, 0), (2, 0), (0, 2)],
    )
    return tuple(
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )


def test_bb_xz_isometry_replays_explicit_matrix_identity():
    hx, hz, _, _ = _matrices()
    report = verify_bb_xz_sector_isometry(hx, hz, ell=3, m=4)

    assert report["verified"] is True
    assert report["permutation_bijective"] is True
    assert report["permutation_involutive"] is True
    assert report["x_rowspace_maps_to_z"] is True
    assert report["z_rowspace_maps_to_x"] is True
    assert report["weight_preserving"] is True
    assert report["canonical_sector"] == "X"
    assert report["covered_sectors"] == ["X", "Z"]


def test_bb_xz_isometry_permutation_is_an_involution():
    permutation = bb_xz_inversion_block_swap_permutation(5, 6)

    assert len(np.unique(permutation)) == 60
    assert np.array_equal(permutation[permutation], np.arange(60))


def test_bb_xz_isometry_fails_closed_for_tampered_matrix():
    hx, hz, _, _ = _matrices()
    tampered = hz.copy()
    tampered[0, 0] ^= 1

    report = verify_bb_xz_sector_isometry(hx, tampered, ell=3, m=4)

    assert report["verified"] is False
    assert not (
        report["x_rowspace_maps_to_z"]
        and report["z_rowspace_maps_to_x"]
        and report["css_commutation"]
    )


def test_bb_xz_isometry_rejects_wrong_geometry():
    hx, hz, _, _ = _matrices()

    report = verify_bb_xz_sector_isometry(hx, hz, ell=2, m=4)

    assert report["verified"] is False
