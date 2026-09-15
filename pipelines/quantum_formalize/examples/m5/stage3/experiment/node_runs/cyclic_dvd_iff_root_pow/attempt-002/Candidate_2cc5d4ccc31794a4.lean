import FrozenTarget_2cc5d4ccc31794a4
theorem M5.Period.cyclic_dvd_iff_root_pow : QuantumHarnessFrozenTarget := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1
  intro F N
  have hpoly : -(1 : M5.BinaryPolynomial) = 1 := CharTwo.neg_eq _
  have hroot : -(1 : AdjoinRoot F) = 1 := by
    simpa only [map_neg, map_one] using congrArg (AdjoinRoot.mk F) hpoly
  rw [← AdjoinRoot.mk_eq_zero]
  simp [M5.cyclicModulus, map_add, map_pow, AdjoinRoot.mk_X,
    add_eq_zero_iff_eq_neg, hroot]
