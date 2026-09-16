import M8Cutoff

theorem M8.Cutoff.anchor_trial_envelope : ∀ (N a b : ℕ), a ≤ N → b ≤ N → 2*N*a*b ≤ 2*N^3 := by
  change ∀ (N a b : ℕ), a ≤ N → b ≤ N → 2 * N * a * b ≤ 2 * N ^ 3
  intro N a b ha hb
  calc
    2 * N * a * b ≤ 2 * N * N * N :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (2 * N) ha) hb
    _ = 2 * N ^ 3 := by ring

theorem M8.Cutoff.bit_length_limit : ∀ N : ℕ, M8.Cutoff.limit N = min (N-1) (Nat.log2 (N+1)) := by
  change ∀ N : ℕ, M8.Cutoff.limit N = min (N - 1) (Nat.log2 (N + 1))
  intro N
  simp only [M8.Cutoff.limit, Nat.log2_eq_log_two]

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

theorem M8.Cutoff.coefficient_capacity : ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2^R * 8^N < 2^(4*(N+1)) := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2 ^ R * 8 ^ N < 2 ^ (4 * (N + 1))
  intro N R hR
  have hlimit := (M8.Cutoff.limit_bounds N).1
  have hRN : R ≤ N := by omega
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8, ← pow_mul, ← pow_add]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem M8.Cutoff.state_bound : ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2^R ≤ N+1 := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 2 ^ R ≤ N + 1
  intro N R hR
  have hlog : R ≤ Nat.log 2 (N + 1) := le_trans hR (M8.Cutoff.limit_bounds N).2.1
  exact Nat.pow_le_of_le_log (by simp) hlog

theorem M8.Cutoff.indexed_storage_envelope : ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N^2 * 2^R ≤ (N+1)^3 := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N ^ 2 * 2 ^ R ≤ (N + 1) ^ 3
  intro N R hR
  calc
    N ^ 2 * 2 ^ R ≤ N ^ 2 * (N + 1) :=
      Nat.mul_le_mul_left _ (M8.Cutoff.state_bound N R hR)
    _ ≤ (N + 1) ^ 3 := by nlinarith

theorem M8.Cutoff.state_square : ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 4^R ≤ (N+1)^2 := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → 4 ^ R ≤ (N + 1) ^ 2
  intro N R hR
  have h := M8.Cutoff.state_bound N R hR
  calc
    4 ^ R = 2 ^ R * 2 ^ R := by rw [← mul_pow]; rfl
    _ ≤ (N + 1) * (N + 1) := Nat.mul_le_mul h h
    _ = (N + 1) ^ 2 := (pow_two (N + 1)).symm

theorem M8.Cutoff.indexed_work_envelopes : ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N^3 * 4^R ≤ (N+1)^5 ∧ N^4 * 4^R ≤ (N+1)^6 := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N^3 * 4^R ≤ (N+1)^5 ∧ N^4 * 4^R ≤ (N+1)^6
  intro N R hR
  have hs := M8.Cutoff.state_square N R hR
  have hp : ∀ k : ℕ, N ^ k ≤ (N + 1) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simpa only [pow_succ] using Nat.mul_le_mul ih (Nat.le_succ N)
  constructor
  · calc
      N ^ 3 * 4 ^ R ≤ (N + 1) ^ 3 * (N + 1) ^ 2 := Nat.mul_le_mul (hp 3) hs
      _ = (N + 1) ^ 5 := by ring
  · calc
      N ^ 4 * 4 ^ R ≤ (N + 1) ^ 4 * (N + 1) ^ 2 := Nat.mul_le_mul (hp 4) hs
      _ = (N + 1) ^ 6 := by ring
#print axioms M8.Cutoff.anchor_trial_envelope
#print axioms M8.Cutoff.bit_length_limit
#print axioms M8.Cutoff.limit_bounds
#print axioms M8.Cutoff.coefficient_capacity
#print axioms M8.Cutoff.state_bound
#print axioms M8.Cutoff.indexed_storage_envelope
#print axioms M8.Cutoff.state_square
#print axioms M8.Cutoff.indexed_work_envelopes
