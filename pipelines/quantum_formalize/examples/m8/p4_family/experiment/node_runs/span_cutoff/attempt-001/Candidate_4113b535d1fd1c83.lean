import FrozenTarget_4113b535d1fd1c83
theorem M8.P4Family.span_cutoff : QuantumHarnessFrozenTarget := by
  intro N inst hN
  have hv (k : ℕ) : (k : ZMod N).val ≤ k := by
    rw [ZMod.val_natCast]
    exact Nat.mod_le _ _
  have hs : ∀ i ∈ M8.P4Family.support N, i.val ≤ 3 := by
    intro i hi
    simp only [M8.P4Family.support, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact (hv 0).trans (by omega)
    · exact (hv 1).trans (by omega)
    · exact (hv 2).trans (by omega)
    · exact hv 3
  have hspan : M8.Anchor.span (M8.P4Family.recipe N) ≤ 3 := by
    apply (M8.Anchor.span_le N (M8.P4Family.recipe N) 3).mpr
    exact ⟨hs, hs⟩
  apply hspan.trans
  rw [M8.Cutoff.bit_length_limit]
  apply le_min (by omega)
  have hm : Nat.log2 8 ≤ Nat.log2 (N + 1) := by
    first
    | exact Nat.log2_le_log2 (by omega)
    | exact Nat.log2_mono (by omega)
    | exact Nat.log2_monotone (by omega)
  norm_num at hm ⊢
  exact hm
