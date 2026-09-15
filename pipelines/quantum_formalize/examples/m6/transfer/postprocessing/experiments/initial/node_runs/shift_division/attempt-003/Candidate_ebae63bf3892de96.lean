import FrozenTarget_ebae63bf3892de96
theorem M6.ActualTransfer.shift_division : QuantumHarnessFrozenTarget := by
  change ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2 : ℤ) ^ k
  intro z k
  simpa using (Int.shiftRight_eq_div_pow z k)
