import M6Postprocessing

theorem M6.ActualTransfer.shift_division : ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2:ℤ)^k := by
  intro z k
  simpa only [Int.shiftRight_eq, Nat.cast_pow, Nat.cast_ofNat] using Int.shiftRight_eq_div_pow z k

theorem M6.ActualTransfer.shifted_coefficient_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), M6.ActualTransfer.shiftedCoefficient N a b P d = (M6.ActualTransfer.Q N a b P).coeff d := by
  intro N inst a b P d
  simp [M6.ActualTransfer.shiftedCoefficient, M6.ActualTransfer.Q,
    Polynomial.coeff_sub, M6.Normalize.divide_coeff,
    M6.ActualTransfer.shift_division]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.shiftedScan N a b P = M6.Pinned.firstPositive (2*N) (M6.ActualTransfer.Q N a b P)
