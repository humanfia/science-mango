import M6Postprocessing

theorem M6.ActualTransfer.shift_division : ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2:ℤ)^k := by
  intro z k
  simpa only [Int.shiftRight_eq, Nat.cast_pow, Nat.cast_ofNat] using Int.shiftRight_eq_div_pow z k
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), M6.ActualTransfer.shiftedCoefficient N a b P d = (M6.ActualTransfer.Q N a b P).coeff d
