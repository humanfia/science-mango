import FrozenTarget_c099b99235250443
theorem M6.Coordinates.modulus_monic_degree : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N
  intro N inst
  change (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).Monic ∧ (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).natDegree = N
  constructor
  · simpa only [Polynomial.C_1] using (Polynomial.monic_X_pow_add_C (1 : ZMod 2) (NeZero.ne N))
  · simpa only [Polynomial.C_1] using (Polynomial.natDegree_X_pow_add_C (n := N) (r := (1 : ZMod 2)))
