import FrozenTarget_48dae6bee17ae628
theorem M7.RawCoverage.root_within : QuantumHarnessFrozenTarget := by
  intro N inst S
  classical
  have hr := M7.PrefixBits.root N (NeZero.pos N)
  rw [hr.1, hr.2.2.1]
  change ({0} ⊆ S.image ZMod.val ∧ S.image ZMod.val ⊆ {0} ∪ (Finset.range N \ {0})) ↔ (0 : ZMod N) ∈ S
  constructor
  · intro h
    have hz := h.1 (Finset.mem_singleton_self 0)
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hz
    have ha0 : a = 0 := ZMod.val_injective (by simpa using hav)
    simpa [ha0] using ha
  · intro h
    constructor
    · apply Finset.singleton_subset_iff.mpr
      exact Finset.mem_image.mpr ⟨0, h, by simp⟩
    · intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      by_cases hz : a.val = 0
      · exact Finset.mem_union.mpr (Or.inl (by simpa using hz))
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_range.mpr (ZMod.val_lt a), by simpa using hz⟩
