import M6RecipeIsometries


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a
