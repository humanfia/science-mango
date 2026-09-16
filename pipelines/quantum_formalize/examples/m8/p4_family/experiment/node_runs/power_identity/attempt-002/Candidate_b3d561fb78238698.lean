import FrozenTarget_b3d561fb78238698
theorem M8.P4Family.power_identity : QuantumHarnessFrozenTarget := by
  change (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial (ZMod 2)) = (Polynomial.X + 1) ^ 3
  have h2 : (2 : Polynomial (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : Polynomial (ZMod 2)) = 1 := by
    calc
      (3 : Polynomial (ZMod 2)) = 2 + 1 := by ring
      _ = 1 := by rw [h2, zero_add]
  calc
    (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial (ZMod 2)) = Polynomial.X ^ 3 + 3 * Polynomial.X ^ 2 + 3 * Polynomial.X + 1 := by
      rw [h3]
      ring
    _ = (Polynomial.X + 1) ^ 3 := by ring
