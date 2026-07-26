import numpy as np

from evaluation.noncss_certificate import (
    solve_symplectic_direction,
    verify_symplectic_direction,
)


def test_symplectic_evidence_contains_and_validates_witness():
    # [[2,1,1]] with stabilizer XX; target logical ZI.
    stabilizer = np.array([[1, 1, 0, 0]], dtype=np.uint8)
    target = np.array([0, 0, 1, 0], dtype=np.uint8)
    evidence = solve_symplectic_direction(stabilizer, target, timeout=10)
    assert evidence["success"] is True
    assert evidence["objective"] == 1
    assert evidence["mip_gap"] == 0.0
    assert evidence["mip_dual_bound"] == 1.0
    from evaluation.certificate import pack_vector
    evidence["logical_index"] = 0
    evidence["target_logical"] = pack_vector(target)
    assert verify_symplectic_direction(evidence, stabilizer, target) == []


def test_symplectic_evidence_rejects_forged_objective():
    stabilizer = np.array([[1, 1, 0, 0]], dtype=np.uint8)
    target = np.array([0, 0, 1, 0], dtype=np.uint8)
    evidence = solve_symplectic_direction(stabilizer, target, timeout=10)
    from evaluation.certificate import pack_vector
    evidence["target_logical"] = pack_vector(target)
    evidence["objective"] = 2
    assert verify_symplectic_direction(evidence, stabilizer, target)
