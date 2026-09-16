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

theorem M8.Cutoff.state_bound : ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2^R ≤ N+1 := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2 ^ R ≤ N + 1
  intro N R hR
  have hlog : R ≤ Nat.log 2 (N + 1) := le_trans hR (M8.Cutoff.limit_bounds N).2.1
  exact Nat.pow_le_of_le_log (by simp) hlog

theorem M8.Cutoff.state_square : ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 4^R ≤ (N+1)^2 := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 4 ^ R ≤ (N + 1) ^ 2
  intro N R hR
  have h := M8.Cutoff.state_bound N R hR
  calc
    4 ^ R = 2 ^ R * 2 ^ R := by rw [← mul_pow]; rfl
    _ ≤ (N + 1) * (N + 1) := Nat.mul_le_mul h h
    _ = (N + 1) ^ 2 := (pow_two (N + 1)).symm
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N^3 * 4^R ≤ (N+1)^5 ∧ N^4 * 4^R ≤ (N+1)^6
