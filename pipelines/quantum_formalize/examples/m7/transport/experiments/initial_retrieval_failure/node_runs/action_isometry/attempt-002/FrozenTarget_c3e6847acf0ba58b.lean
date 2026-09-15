import M7Transport

theorem M7.Transport.affine_indicator : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N) (u : (ZMod N)ˣ) (s : ZMod N), M7.Supports.indicator (A.image (M7.Action.affine u s)) = M6.RecipeIsometries.shift N s (M6.RecipeIsometries.multiply N u (M7.Supports.indicator A)) := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), Function.Bijective (M7.Transport.Xmap g) ∧ ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Xmap g v ∈ M7.Transport.BX (M7.Action.act g c) ↔ v ∈ M7.Transport.BX c) ∧ (M7.Transport.Xmap g v ∈ M7.Transport.CX (M7.Action.act g c) ↔ v ∈ M7.Transport.CX c) ∧ M6.Pinned.weight (M7.Transport.Xmap g v) = M6.Pinned.weight v
