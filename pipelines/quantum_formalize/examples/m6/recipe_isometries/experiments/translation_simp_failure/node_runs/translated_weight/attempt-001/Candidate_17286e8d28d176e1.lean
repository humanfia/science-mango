import FrozenTarget_17286e8d28d176e1
theorem M6.RecipeIsometries.translated_weight : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.translateWord N r s z) = M6.Physical.wordWeight N z
  intro N _ r s z
  change M6.Physical.weight N (fun i => z.1 (i - r)) + M6.Physical.weight N (fun i => z.2 (i - s)) = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  have hr := M6.RecipeIsometries.permutation_weight N (Equiv.addRight (-r)) z.1
  have hs := M6.RecipeIsometries.permutation_weight N (Equiv.addRight (-s)) z.2
  change M6.Physical.weight N (fun i => z.1 (i + -r)) = M6.Physical.weight N z.1 at hr
  change M6.Physical.weight N (fun i => z.2 (i + -s)) = M6.Physical.weight N z.2 at hs
  simpa only [sub_eq_add_neg] using congrArg₂ Nat.add hr hs
