import FrozenTarget_560e940ee665b614
theorem M6.Coordinates.modulus_monic_degree : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N
  intro N inst
  unfold M6.Cyclic.modulus
  constructor
  · simpa only [Polynomial.C_1] using (show (Polynomial.X ^ N + Polynomial.C (1 : ZMod 2)).Monic from by
      apply Polynomial.monic_X_pow_add_C
      first | exact NeZero.pos N | exact NeZero.ne N)
  · simpa only [Polynomial.C_1] using (show (Polynomial.X ^ N + Polynomial.C (1 : ZMod 2)).natDegree = N from by
      apply Polynomial.natDegree_X_pow_add_C
      first | exact NeZero.pos N | exact NeZero.ne N)
