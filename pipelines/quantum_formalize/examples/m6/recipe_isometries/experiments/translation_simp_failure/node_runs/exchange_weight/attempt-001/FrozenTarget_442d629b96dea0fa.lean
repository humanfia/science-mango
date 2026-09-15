import M6RecipeIsometries


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.exchange N z) = M6.Physical.wordWeight N z
