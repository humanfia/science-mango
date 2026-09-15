import FrozenTarget_c9b15ed674b02ede
theorem M5.Period.cyclic_dvd_iff_root_pow : QuantumHarnessFrozenTarget := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1
  intro F N
  rw [← AdjoinRoot.mk_eq_zero]
  simp [M5.cyclicModulus, map_add, map_pow, map_sub, AdjoinRoot.mk_X,
    add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
