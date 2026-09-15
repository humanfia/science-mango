import FrozenTarget_7f7a3856930ca1bf
theorem M5.ArithmeticSubset.n_exact : QuantumHarnessFrozenTarget := by
  intro P hP W k z
  classical
  unfold M5.ArithmeticSubset.n
  rw [M5.ArithmeticSubset.numerator_exact P hP W k z]
  have h : (2 : ℤ) ^ P.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [h]
