import FrozenTarget_b433bc89ef7c9be5
theorem M6.ActualTransfer.shift_division : QuantumHarnessFrozenTarget := by
  intro z k
  simpa only [Int.shiftRight_eq, Nat.cast_pow, Nat.cast_ofNat] using Int.shiftRight_eq_div_pow z k
