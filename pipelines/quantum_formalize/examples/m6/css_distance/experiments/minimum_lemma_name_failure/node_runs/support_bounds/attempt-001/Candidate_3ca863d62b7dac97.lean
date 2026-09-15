import FrozenTarget_3ca863d62b7dac97
theorem M6.CSS.support_bounds : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (p : M6.CSS.Pauli m), M6.Pinned.weight p.1 ≤ M6.CSS.weight p ∧ M6.Pinned.weight p.2 ≤ M6.CSS.weight p
  intro m p
  classical
  unfold M6.Pinned.weight M6.CSS.weight M6.CSS.support
  constructor
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inl hi
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inr hi
