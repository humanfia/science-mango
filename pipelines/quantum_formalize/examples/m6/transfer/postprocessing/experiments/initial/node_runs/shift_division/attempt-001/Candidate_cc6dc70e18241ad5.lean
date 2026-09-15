import FrozenTarget_cc6dc70e18241ad5
theorem M6.ActualTransfer.shift_division : QuantumHarnessFrozenTarget := by
  change ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2 : ℤ)^k
  intro z k
  simpa using Int.shiftRight_eq_div_pow z k
