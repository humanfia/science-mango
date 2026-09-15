import FrozenTarget_d2e874b1758a750f
theorem M6.RecipeIsometries.conv_shift : QuantumHarnessFrozenTarget := by
  intro N _ r s a h
  classical
  funext i
  change Finset.sum Finset.univ (fun k : ZMod N => a (k - r) * h (i - k - s)) =
    Finset.sum Finset.univ (fun k : ZMod N => a k * h (i - (r + s) - k))
  calc
    _ = Finset.sum Finset.univ (fun k : ZMod N => a ((k + r) - r) * h (i - (k + r) - s)) :=
      ((Equiv.addRight r).sum_comp (fun k : ZMod N => a (k - r) * h (i - k - s))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [add_sub_cancel_right]
      have hi : i - (k + r) - s = i - (r + s) - k := by ring
      rw [hi]
