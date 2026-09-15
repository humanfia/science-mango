import FrozenTarget_54c6f17b08fb3711
theorem M5.recovery_inclusion_positive : QuantumHarnessFrozenTarget := by
  by
    change ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included
    intro total excluded included htotal hpos hexcluded
    rw [hexcluded, Nat.zero_add] at htotal
    rw [htotal] at hpos
    exact hpos
