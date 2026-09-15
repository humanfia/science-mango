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

theorem M6.RecipeIsometries.shift_laws : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.shift N 0 a = a ∧ M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) = a ∧ (M6.RecipeIsometries.shift N r a = 0 ↔ a = 0) := by
  intro N inst r a
  have hinv (b : M6.RecipeIsometries.Block N) :
      M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r b) = b := by
    funext i
    simp [M6.RecipeIsometries.shift, sub_eq_add_neg, add_assoc]
  refine ⟨?_, hinv a, ?_⟩
  · funext i
    simp [M6.RecipeIsometries.shift]
  · constructor
    · intro h
      calc
        a = M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) := (hinv a).symm
        _ = M6.RecipeIsometries.shift N (-r) 0 := congrArg (M6.RecipeIsometries.shift N (-r)) h
        _ = 0 := rfl
    · intro h
      subst a
      rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b h : M6.RecipeIsometries.Block N), M6.Physical.boundary N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) h = M6.RecipeIsometries.translateWord N r s (M6.Physical.boundary N a b h)
