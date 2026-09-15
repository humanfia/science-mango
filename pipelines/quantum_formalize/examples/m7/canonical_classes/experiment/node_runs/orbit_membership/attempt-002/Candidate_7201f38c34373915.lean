import FrozenTarget_7201f38c34373915
theorem M7.CanonicalClasses.orbit_membership : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c y : M7.Action.Recipe N, y ∈ M7.ActualOrbit.orbit c ↔ M7.CanonicalOuter.canonical y = M7.CanonicalOuter.canonical c
  intro N _ c y
  classical
  simp only [M7.ActualOrbit.orbit, Finset.mem_image, Finset.mem_univ, true_and]
  exact (M7.CanonicalOuter.orbit_complete N c y).trans eq_comm
