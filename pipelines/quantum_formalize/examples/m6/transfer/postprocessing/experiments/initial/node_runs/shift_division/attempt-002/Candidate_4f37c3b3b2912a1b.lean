import FrozenTarget_4f37c3b3b2912a1b
theorem M6.ActualTransfer.shift_division : QuantumHarnessFrozenTarget := by
  change ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2 : ℤ) ^ k
  intro z k
  simpa only [Int.shiftRight_natCast_right, Int.natCast_pow, Int.natCast_ofNat] using (Int.shiftRight_eq_div_pow z k)
