import numpy as np

from evaluation.certificate import pack_vector
from evaluation.noncss_certificate import (
    solve_symplectic_direction,
    verify_symplectic_witness,
)


def test_nonoptimal_incumbent_is_still_a_verifiable_upper_witness():
    stabilizer = np.array([[1, 1, 0, 0]], dtype=np.uint8)
    target = np.array([0, 0, 1, 0], dtype=np.uint8)
    evidence = solve_symplectic_direction(stabilizer, target, timeout=10)
    evidence["target_logical"] = pack_vector(target)
    evidence["success"] = False
    evidence["mip_gap"] = 0.5
    assert verify_symplectic_witness(evidence, stabilizer, target) == []
