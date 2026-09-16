import FrozenTarget_e0ec82c71acd9b52
theorem M8.MixedFamily.span_cutoff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Anchor.span (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N
  intro N inst hN
  classical
  have hspan : M8.Anchor.span (M8.MixedFamily.recipe N) ≤ 2 := by
    apply (M8.Anchor.span_le N (M8.MixedFamily.recipe N) 2).2
    constructor
    · intro i hi
      change i ∈ ({0, 1} : Finset (ZMod N)) at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp
      · change ((1 : ℕ) : ZMod N).val ≤ 2
        rw [ZMod.val_natCast]
        exact (Nat.mod_le 1 N).trans (by decide)
    · intro i hi
      change i ∈ ({0, 2} : Finset (ZMod N)) at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp
      · change ((2 : ℕ) : ZMod N).val ≤ 2
        rw [ZMod.val_natCast]
        exact Nat.mod_le 2 N
  apply hspan.trans
  have hlog : 2 ≤ Nat.log 2 (N + 1) := by
    have h := Nat.log_mono_right (b := 2) (show 4 ≤ N + 1 by omega)
    norm_num at h
    exact h
  first
  | change 2 ≤ min (N - 1) (Nat.log 2 (N + 1))
    exact le_min (by omega) hlog
  | rw [M8.Cutoff.bit_length_limit]
    apply le_min (by omega)
    first
    | simpa only [Nat.log_two_eq_log2] using hlog
    | simpa only [Nat.log2_eq_log_two] using hlog
