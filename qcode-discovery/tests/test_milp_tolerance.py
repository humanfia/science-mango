import numpy as np

from evaluation.certificate import pack_vector
from evaluation.noncss_certificate import (
    solve_symplectic_direction,
    verify_symplectic_direction,
)


def test_highs_dual_bound_roundoff_is_not_a_false_rejection():
    stabilizer = np.array([[1, 1, 0, 0]], dtype=np.uint8)
    target = np.array([0, 0, 1, 0], dtype=np.uint8)
    evidence = solve_symplectic_direction(stabilizer, target, timeout=10)
    evidence["target_logical"] = pack_vector(target)
    evidence["mip_dual_bound"] = float(evidence["objective"]) - 1e-12
    assert verify_symplectic_direction(evidence, stabilizer, target) == []
