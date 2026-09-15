import M6RecipeIsometries


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.multiply N 1 a = a ∧ M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) = a ∧ (M6.RecipeIsometries.multiply N u a = 0 ↔ a = 0)
