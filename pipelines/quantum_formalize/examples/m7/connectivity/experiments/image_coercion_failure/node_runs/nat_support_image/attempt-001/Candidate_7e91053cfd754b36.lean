import FrozenTarget_7e91053cfd754b36
theorem M7.Connectivity.nat_support_image : QuantumHarnessFrozenTarget := by
  intro N inst A B
  classical
  unfold M7.Supports.natSupport
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rcases Finset.mem_union.mp hn with hn | hn
    · rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
      exact Or.inl (by simpa only [ZMod.natCast_zmod_val] using ha)
    · rcases Finset.mem_image.mp hn with ⟨b, hb, rfl⟩
      exact Or.inr (by simpa only [ZMod.natCast_zmod_val] using hb)
  · intro hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rcases hx with hx | hx
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
