import M6TransferResources

theorem M6.Transfer.state_count : ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2^R := by
  change ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2 ^ R
  intro R
  simp [M6.Transfer.Memory, M6.Transfer.Bit, Fintype.card_fun, ZMod.card]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2*N+1) * 4^R
