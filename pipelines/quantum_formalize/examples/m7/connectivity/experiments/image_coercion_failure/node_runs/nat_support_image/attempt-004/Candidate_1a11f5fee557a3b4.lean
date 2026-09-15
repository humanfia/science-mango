import FrozenTarget_1a11f5fee557a3b4
theorem M7.Connectivity.nat_support_image : QuantumHarnessFrozenTarget := by
  intro N inst A B
  classical
  apply Set.ext
  intro x
  change (∃ n : ℕ, n ∈ (A.image (fun a => a.val) ∪ B.image (fun b => b.val)) ∧ (n : ZMod N) = x) ↔ (x ∈ A ∨ x ∈ B)
  constructor
  · rintro ⟨n, hn, hnx⟩
    rcases Finset.mem_union.mp hn with ha | hb
    · rcases Finset.mem_image.mp ha with ⟨a, ha, rfl⟩
      have hax : a = x := by
        simpa only [ZMod.natCast_zmod_val] using hnx
      exact Or.inl (hax ▸ ha)
    · rcases Finset.mem_image.mp hb with ⟨b, hb, rfl⟩
      have hbx : b = x := by
        simpa only [ZMod.natCast_zmod_val] using hnx
      exact Or.inr (hbx ▸ hb)
  · intro hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rcases hx with ha | hb
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x, ha, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hb, rfl⟩))
