import M6RecipeIsometries


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b h : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.boundary N b a h = M6.RecipeIsometries.exchange N (M6.Physical.boundary N a b h) ∧ M6.Physical.syndrome N b a (M6.RecipeIsometries.exchange N z) = M6.Physical.syndrome N a b z
