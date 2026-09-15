import FrozenTarget_ed82b7d7bc0b751e
theorem M7.Connectivity.nat_support_image : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (fun a : ℕ => (a : ZMod N)) '' ((M7.Supports.natSupport A ∪ M7.Supports.natSupport B : Finset ℕ) : Set ℕ) = (A : Set (ZMod N)) ∪ (B : Set (ZMod N))
  intro N inst A B
  classical
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    change (n : ZMod N) ∈ A ∨ (n : ZMod N) ∈ B
    rcases Finset.mem_union.mp hn with ha | hb
    · change n ∈ A.image (fun a => a.val) at ha
      rcases Finset.mem_image.mp ha with ⟨a, ha, rfl⟩
      left
      simpa only [ZMod.natCast_zmod_val] using ha
    · change n ∈ B.image (fun b => b.val) at hb
      rcases Finset.mem_image.mp hb with ⟨b, hb, rfl⟩
      right
      simpa only [ZMod.natCast_zmod_val] using hb
  · intro hx
    change x ∈ A ∨ x ∈ B at hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    change x.val ∈ A.image (fun a => a.val) ∪ B.image (fun b => b.val)
    rcases hx with ha | hb
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x, ha, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hb, rfl⟩))
