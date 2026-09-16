import FrozenTarget_5dee3819b37b3aa2
theorem M8.MixedFamily.span_cutoff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Anchor.span (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N
  intro N inst hN
  have hval (k : ℕ) (hk : k ≤ 2) : (k : ZMod N).val ≤ 2 := by
    rw [ZMod.val_natCast]
    exact (Nat.mod_le k N).trans hk
  have hspan : M8.Anchor.span (M8.MixedFamily.recipe N) ≤ 2 := by
    apply (M8.Anchor.span_le N (M8.MixedFamily.recipe N) 2).mpr
    change (∀ i ∈ ({0, 1} : Finset (ZMod N)), i.val ≤ 2) ∧
      (∀ i ∈ ({0, 2} : Finset (ZMod N)), i.val ≤ 2)
    constructor
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simpa only [Nat.cast_zero] using hval 0 (by omega)
      · simpa only [Nat.cast_one] using hval 1 (by omega)
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simpa only [Nat.cast_zero] using hval 0 (by omega)
      · simpa using hval 2 (by omega)
  apply hspan.trans
  rw [M8.Cutoff.bit_length_limit, Nat.log2_eq_log_two]
  apply le_min
  · omega
  · have hlog := Nat.log_mono_right (b := 2) (show 4 ≤ N + 1 by omega)
    norm_num at hlog
    exact hlog
