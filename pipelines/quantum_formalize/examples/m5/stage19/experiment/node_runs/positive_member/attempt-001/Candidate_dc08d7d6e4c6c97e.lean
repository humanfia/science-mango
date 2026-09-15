import FrozenTarget_dc08d7d6e4c6c97e
theorem M5.PhysicalBridge.positive_member : QuantumHarnessFrozenTarget := by
  change ∀ A : Finset ℕ, 2 ≤ A.card → 0 ∈ A → ∃ a ∈ A, 0 < a
  intro A hcard hzero
  by_contra h
  have hsub : A ⊆ {0} := by
    intro a ha
    have haz : a = 0 := by
      by_contra hne
      exact h ⟨a, ha, Nat.pos_of_ne_zero hne⟩
    simpa only [Finset.mem_singleton] using haz
  have hle : A.card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  omega
