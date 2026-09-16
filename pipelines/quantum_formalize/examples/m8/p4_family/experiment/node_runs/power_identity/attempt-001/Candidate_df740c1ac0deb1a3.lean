import FrozenTarget_df740c1ac0deb1a3
theorem M8.P4Family.power_identity : QuantumHarnessFrozenTarget := by
  change (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial (ZMod 2)) = (Polynomial.X + 1) ^ 3
  have h : (3 : Polynomial (ZMod 2)) = 1 := by
    simpa using congrArg (Polynomial.C : ZMod 2 → Polynomial (ZMod 2)) (show (3 : ZMod 2) = 1 by decide)
  calc
    _ = Polynomial.X ^ 3 + 3 * Polynomial.X ^ 2 + 3 * Polynomial.X + 1 := by
      rw [h]
      ring
    _ = (Polynomial.X + 1) ^ 3 := by ring
