import FrozenTarget_4f4ed5088457615a
theorem M6.ActualTransfer.shift_division : QuantumHarnessFrozenTarget := by
  change ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2 : ℤ)^k
  intro z k
  calc
    Int.shiftRight z k = z >>> k := Int.shiftRight_natCast_right z k
    _ = z / (2 : ℤ)^k := Int.shiftRight_eq_div_pow z k
