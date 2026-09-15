import FrozenTarget_1aee8e6c1775fc72
theorem M7.StreamingIndices.all_fin : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (p : Fin n → Bool), M7.StreamingIndices.allFin n p = true ↔ ∀ j : Fin n, p j = true
  intro n p
  unfold M7.StreamingIndices.allFin
  rw [M7.StreamingIndices.cursor_interval]
  constructor
  · intro h j
    exact h j (Nat.zero_le _) (by simpa only [Nat.zero_add] using j.isLt)
  · intro h j _ _
    exact h j
