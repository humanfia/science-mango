import FrozenTarget_f0c3e6edb6449c98
theorem M7.QuerySectors.all_membership : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N ↔ F.Monic ∧ F ∣ M6.Cyclic.modulus N
  intro N inst F
  constructor
  · exact M7.QuerySectors.all_sound N F
  · intro h
    exact M7.QuerySectors.all_complete N F h.1 h.2
