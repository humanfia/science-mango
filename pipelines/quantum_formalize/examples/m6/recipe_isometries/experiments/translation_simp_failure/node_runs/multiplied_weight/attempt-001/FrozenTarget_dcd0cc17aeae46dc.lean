import M6RecipeIsometries

theorem M6.RecipeIsometries.permutation_weight : ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a := by
  change ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a
  intro N _ e a
  classical
  unfold M6.Physical.weight
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simpa using hj
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.multiplyWord N u z) = M6.Physical.wordWeight N z
