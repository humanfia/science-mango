import M6RecipeIsometries

theorem M6.RecipeIsometries.conv_shift : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s h) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.conv N a h) := by
  intro N inst r s a h
  classical
  funext i
  change Finset.sum Finset.univ (fun k : ZMod N => a (k - r) * h (i - k - s)) =
    Finset.sum Finset.univ (fun k : ZMod N => a k * h (i - (r + s) - k))
  refine (Equiv.sum_comp (Equiv.addRight r)
    (fun k : ZMod N => a (k - r) * h (i - k - s))).symm.trans ?_
  change Finset.sum Finset.univ (fun k : ZMod N => a (k + r - r) * h (i - (k + r) - s)) = _
  apply Finset.sum_congr rfl
  intro k hk
  have hi : i - (k + r) - s = i - (r + s) - k := by ring
  simp only [add_sub_cancel_right, hi]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) (M6.RecipeIsometries.translateWord N r s z) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.syndrome N a b z)
