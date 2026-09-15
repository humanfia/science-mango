import FrozenTarget_67ff66c935128673
theorem M7.ActualOrbit.stabilizer_positive : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), 0 < M7.ActualOrbit.stabilizerCount c
  intro N inst c
  exact M7.OrbitFibers.stabilizer_positive (M7.Action.Record N) (M7.Action.Recipe N) c
