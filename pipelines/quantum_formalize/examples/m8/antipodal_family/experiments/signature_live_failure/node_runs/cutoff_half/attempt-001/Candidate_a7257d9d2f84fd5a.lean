import FrozenTarget_a7257d9d2f84fd5a
theorem M8.AntipodalFamily.cutoff_half : QuantumHarnessFrozenTarget := by
  change ∀ v : ℕ, 3 ≤ v → M8.Cutoff.limit (2^v) = v ∧ v < 2^(v-1)
  intro v hv
  have hp : ∀ k : ℕ, k + 3 < (2 : ℕ)^(k + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have he : (2 : ℕ)^(Nat.succ k + 2) = 2^(k + 2) * 2 := by
        rw [show Nat.succ k + 2 = (k + 2) + 1 by omega, pow_succ]
      rw [he]
      omega
  have hhalf := hp (v - 3)
  have hx : v - 3 + 3 = v := by omega
  have hy : v - 3 + 2 = v - 1 := by omega
  rw [hx, hy] at hhalf
  have he : (2 : ℕ)^v = 2^(v-1) * 2 := by
    calc
      2^v = 2^((v-1)+1) := congrArg (fun n : ℕ => (2 : ℕ)^n) (by omega)
      _ = 2^(v-1) * 2 := pow_succ _ _
  have hmin : v ≤ (2 : ℕ)^v - 1 := by omega
  have hlo : (2 : ℕ)^v ≤ 2^v + 1 := by omega
  have hhi : (2 : ℕ)^v + 1 < 2^(v+1) := by
    rw [pow_succ]
    omega
  have hlog : Nat.log 2 ((2 : ℕ)^v + 1) = v := by
    apply Nat.log_eq_of_pow_le_of_lt_pow <;> omega
  constructor
  · rw [M8.Cutoff.bit_length_limit]
    have hlog2 : Nat.log2 ((2 : ℕ)^v + 1) = v := by
      first
      | simpa only [Nat.log2_eq_log_two] using hlog
      | simpa only [Nat.log_two_eq_log2] using hlog
    rw [hlog2, min_eq_right hmin]
  · exact hhalf
