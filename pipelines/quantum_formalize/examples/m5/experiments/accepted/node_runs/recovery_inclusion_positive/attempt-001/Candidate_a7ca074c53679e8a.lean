import FrozenTarget_a7ca074c53679e8a
theorem M5.recovery_inclusion_positive : QuantumHarnessFrozenTarget := by
  change ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included
  intro total excluded included htotal hpos hexcluded
  simpa only [htotal, hexcluded, Nat.zero_add] using hpos
