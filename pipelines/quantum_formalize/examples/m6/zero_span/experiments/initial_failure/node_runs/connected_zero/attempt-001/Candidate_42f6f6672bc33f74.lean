import FrozenTarget_42f6f6672bc33f74
theorem M6.ZeroSpan.connected_zero : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, M6.Final.Admissible N 1 1 → N = 1
  intro N h
  simp_all [M6.Final.Admissible, Polynomial.support_one]
  <;> aesop
