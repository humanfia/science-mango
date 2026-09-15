import M6RecipeIsometries


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (r : ZMod N) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.shift N 0 a = a ∧ M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) = a ∧ (M6.RecipeIsometries.shift N r a = 0 ↔ a = 0)
