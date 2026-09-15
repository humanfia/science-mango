import FrozenTarget_9cf322ee77f94400
theorem M6.Transfer.boundary_factor_bounds : QuantumHarnessFrozenTarget := by
  classical
  intro m P i s
  by_cases h : P i = none ∨ P i = some s
  · simp only [M6.Character.boundaryFactor, if_pos h]
    constructor
    · have hx : (Polynomial.X : Polynomial ℤ) ^ s.val = Polynomial.monomial s.val 1 := by
        ext n
        simp [Polynomial.coeff_monomial, eq_comm]
      rw [hx, M6.Transfer.mass_basic.2.2.1]
      norm_num
    · have hs := ZMod.val_lt s
      rw [Polynomial.natDegree_X_pow]
      omega
  · simp [M6.Character.boundaryFactor, h, M6.Transfer.mass_basic.1]
