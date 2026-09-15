import FrozenTarget_6c4f3119331bca72
theorem M6.RecipeIsometries.conv_shift : QuantumHarnessFrozenTarget := by
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
