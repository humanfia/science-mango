import FrozenTarget_e7813fdf252eef49
theorem M6.Transfer.post_event_count : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, Fintype.card (M6.Transfer.PostEvent N) = 4 * (2 * N + 1)
  intro N
  simp [M6.Transfer.PostEvent, M6.Transfer.Bit, Fintype.card_prod] <;> ring
