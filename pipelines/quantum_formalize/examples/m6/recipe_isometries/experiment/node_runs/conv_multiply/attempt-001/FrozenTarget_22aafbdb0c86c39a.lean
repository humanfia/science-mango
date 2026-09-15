import M6RecipeIsometries


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiply N u (M6.Physical.conv N a h)
