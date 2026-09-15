import FrozenTarget_a5309cc4d602d5a5
theorem M5.recovery_inclusion_positive : QuantumHarnessFrozenTarget := by
  change ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included
  intro total excluded included hpartition hpositive hexcluded
  rw [hpartition, hexcluded, Nat.zero_add] at hpositive
  exact hpositive
