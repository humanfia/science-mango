import FrozenTarget_6892e0968a2349d4
theorem M7.ActualFactorized.positive_denominator : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, 0 < M7.ActualFactorized.stabilizerNumerator c
  intro N inst c
  rw [M7.ActualFactorized.stabilizer_numerator N c]
  exact M7.ActualOrbit.stabilizer_positive N c
