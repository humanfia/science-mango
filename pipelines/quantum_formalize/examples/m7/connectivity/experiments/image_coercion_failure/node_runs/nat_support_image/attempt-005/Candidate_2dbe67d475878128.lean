import FrozenTarget_2dbe67d475878128
theorem M7.Connectivity.nat_support_image : QuantumHarnessFrozenTarget := by
  classical
  intro N inst A B
  change (fun n : ℕ => (n : ZMod N)) ''
      ((A.image (fun a => a.val) ∪ B.image (fun b => b.val) : Finset ℕ) : Set ℕ) =
      (A : Set (ZMod N)) ∪ (B : Set (ZMod N))
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rcases Finset.mem_union.mp hn with ha | hb
    · rcases Finset.mem_image.mp ha with ⟨a, ha, rfl⟩
      left
      simpa only [ZMod.natCast_zmod_val] using ha
    · rcases Finset.mem_image.mp hb with ⟨b, hb, rfl⟩
      right
      simpa only [ZMod.natCast_zmod_val] using hb
  · intro hx
    refine ⟨x.val, ?_, by simp only [ZMod.natCast_zmod_val]⟩
    rcases hx with ha | hb
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x, ha, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hb, rfl⟩))
