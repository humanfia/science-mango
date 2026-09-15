import FrozenTarget_8b608b6f89ef6e01
theorem M7.Connectivity.nat_support_image : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (fun a : ℕ => (a : ZMod N)) '' ((M7.Supports.natSupport A ∪ M7.Supports.natSupport B : Finset ℕ) : Set ℕ) = (A : Set (ZMod N)) ∪ (B : Set (ZMod N))
  intro N hN A B
  classical
  apply Set.ext
  intro x
  change (∃ n : ℕ, n ∈ M7.Supports.natSupport A ∪ M7.Supports.natSupport B ∧ (n : ZMod N) = x) ↔ (x ∈ A ∨ x ∈ B)
  constructor
  · rintro ⟨n, hn, rfl⟩
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
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rcases hx with ha | hb
    · apply Finset.mem_union.mpr
      left
      change x.val ∈ A.image (fun a => a.val)
      exact Finset.mem_image.mpr ⟨x, ha, rfl⟩
    · apply Finset.mem_union.mpr
      right
      change x.val ∈ B.image (fun b => b.val)
      exact Finset.mem_image.mpr ⟨x, hb, rfl⟩
