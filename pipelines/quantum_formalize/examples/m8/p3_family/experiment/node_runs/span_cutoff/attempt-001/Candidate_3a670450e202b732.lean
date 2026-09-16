import FrozenTarget_3a670450e202b732
theorem M8.P3Family.span_cutoff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.Anchor.span (M8.P3Family.recipe N) ≤ M8.Cutoff.limit N
  intro N inst hN
  classical
  have hs : ∀ i ∈ M8.P3Family.support N, i.val ≤ 2 := by
    intro i hi
    simp only [M8.P3Family.support, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simp
    · change ((1 : ℕ) : ZMod N).val ≤ 2
      rw [ZMod.val_natCast]
      exact le_trans (Nat.mod_le 1 N) (by decide)
    · change ((2 : ℕ) : ZMod N).val ≤ 2
      rw [ZMod.val_natCast]
      exact Nat.mod_le 2 N
  have hspan : M8.Anchor.span (M8.P3Family.recipe N) ≤ 2 := by
    apply (M8.Anchor.span_le N (M8.P3Family.recipe N) 2).2
    exact ⟨hs, hs⟩
  have hlog : 2 ≤ Nat.log 2 (N + 1) := by
    apply (Nat.le_log_iff_pow_le (by decide) (by omega)).2
    norm_num
    omega
  have hlog2 : 2 ≤ Nat.log2 (N + 1) := by
    first
    | simpa only [Nat.log_two_eq_log2] using hlog
    | simpa only [Nat.log2_eq_log] using hlog
    | exact hlog
  apply le_trans hspan
  rw [M8.Cutoff.bit_length_limit]
  exact le_min (by omega) hlog2
