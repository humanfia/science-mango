import FrozenTarget_9b5d64c141775c45
theorem M5.OrderBoundary.range_card : QuantumHarnessFrozenTarget := by
  change ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N
  intro S N h
  have hsub : S ⊆ Finset.range N := by
    intro e he
    exact Finset.mem_range.mpr (h e he)
  simpa only [Finset.card_range] using Finset.card_le_card hsub
