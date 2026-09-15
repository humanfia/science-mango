import FrozenTarget_d2d790a14e2341d9
theorem M7.ResiduePrefix.nat_roundtrip : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst A hA
    change (A.image (fun i : ℕ => (i : ZMod N))).image ZMod.val = A
    rw [Finset.image_image]
    ext i
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨j, hj, hji⟩
      have hv : (j : ZMod N).val = j :=
        ZMod.val_natCast_of_lt (Finset.mem_range.mp (hA hj))
      change (j : ZMod N).val = i at hji
      rw [hv] at hji
      exact hji ▸ hj
    · intro hi
      refine ⟨i, hi, ?_⟩
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (hA hi))
