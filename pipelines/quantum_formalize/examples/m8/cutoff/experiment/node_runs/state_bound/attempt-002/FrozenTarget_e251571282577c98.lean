import M8Cutoff

theorem M8.Cutoff.limit_bounds : ∀ N : ℕ, M8.Cutoff.limit N ≤ N-1 ∧ M8.Cutoff.limit N ≤ Nat.log 2 (N+1) ∧ (0 < N → M8.Cutoff.limit N < N) := by
  change ∀ N : ℕ, M8.Cutoff.limit N ≤ N - 1 ∧ M8.Cutoff.limit N ≤ Nat.log 2 (N + 1) ∧ (0 < N → M8.Cutoff.limit N < N)
  intro N
  have h₁ : M8.Cutoff.limit N ≤ N - 1 := by
    unfold M8.Cutoff.limit
    first | exact min_le_left _ _ | exact min_le_right _ _
  have h₂ : M8.Cutoff.limit N ≤ Nat.log 2 (N + 1) := by
    unfold M8.Cutoff.limit
    first | exact min_le_right _ _ | exact min_le_left _ _
  refine ⟨h₁, h₂, ?_⟩
  intro hN
  exact lt_of_le_of_lt h₁ (Nat.sub_lt hN (by decide))
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2^R ≤ N+1
