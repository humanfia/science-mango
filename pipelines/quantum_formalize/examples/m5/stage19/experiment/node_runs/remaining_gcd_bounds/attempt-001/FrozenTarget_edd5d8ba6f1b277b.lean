import M5PhysicalBridge

theorem M5.PhysicalBridge.positive_member : ∀ A : Finset ℕ, 2 ≤ A.card → 0 ∈ A → ∃ a ∈ A, 0 < a := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A B : Finset ℕ) (e K : ℕ), 2 ≤ B.card → 0 ∈ B → (∀ b ∈ B, b < K) → 0 < M5.PhysicalBridge.remainingGcd A B e ∧ M5.PhysicalBridge.remainingGcd A B e < K
