import M6RecipeIsometries

theorem M6.RecipeIsometries.conv_multiply : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiply N u (M6.Physical.conv N a h) := by
  intro N _ u a h
  classical
  funext i
  change (∑ j : ZMod N, a ((↑(u⁻¹) : ZMod N) * j) * h ((↑(u⁻¹) : ZMod N) * (i - j))) =
    ∑ k : ZMod N, a k * h ((↑(u⁻¹) : ZMod N) * i - k)
  calc
    _ = ∑ k : ZMod N, a ((↑(u⁻¹) : ZMod N) * ((↑u : ZMod N) * k)) *
        h ((↑(u⁻¹) : ZMod N) * (i - (↑u : ZMod N) * k)) :=
      (Equiv.sum_comp u.mulLeft (fun j : ZMod N =>
        a ((↑(u⁻¹) : ZMod N) * j) * h ((↑(u⁻¹) : ZMod N) * (i - j)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [mul_sub, ← mul_assoc]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) (M6.RecipeIsometries.multiplyWord N u z) = M6.RecipeIsometries.multiply N u (M6.Physical.syndrome N a b z)
