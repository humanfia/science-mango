import FrozenTarget_85d0034117784391
theorem M7.Transport.affine_indicator : QuantumHarnessFrozenTarget := by
  intro N inst A u s
  classical
  funext i
  have h : i ∈ A.image (M7.Action.affine u s) ↔
      (↑(u⁻¹) : ZMod N) * (i - s) ∈ A := by
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa [M7.Action.affine, ← mul_assoc] using hj
    · intro hi
      apply Finset.mem_image.mpr
      refine ⟨(↑(u⁻¹) : ZMod N) * (i - s), hi, ?_⟩
      simp [M7.Action.affine, ← mul_assoc]
  simp only [M7.Supports.indicator, M6.RecipeIsometries.shift,
    M6.RecipeIsometries.multiply, h]
