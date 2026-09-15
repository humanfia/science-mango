import FrozenTarget_26defdc7ce60e3e2
theorem M6.Coordinates.block_coeff : QuantumHarnessFrozenTarget := by
  intro N inst h i
  classical
  simp [M6.Coordinates.blockPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Fin.val_eq_val, i.isLt]
