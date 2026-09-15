import M6RecipeIsometries


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b a1 b1 : M6.RecipeIsometries.Block N) (P : M6.RecipeIsometries.Word N → M6.RecipeIsometries.Word N) (H : M6.RecipeIsometries.Block N → M6.RecipeIsometries.Block N), Function.Bijective P → Function.Surjective H → (∀ h, M6.Physical.boundary N a1 b1 (H h) = P (M6.Physical.boundary N a b h)) → (∀ z, M6.Physical.syndrome N a1 b1 (P z) = 0 ↔ M6.Physical.syndrome N a b z = 0) → (∀ z, M6.Physical.wordWeight N (P z) = M6.Physical.wordWeight N z) → Function.Bijective (M6.RecipeIsometries.lift N P) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.boundaryWords N (a1) (b1) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.cycleWords N (a1) (b1) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.lift N P) v) = M6.Pinned.weight v
