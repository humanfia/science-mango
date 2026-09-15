import FrozenTarget_ecd7eec8fd9f63b7
theorem M6.RecipeIsometries.translated_weight : QuantumHarnessFrozenTarget := by
  intro N _ r s z
  change M6.Physical.weight N (M6.RecipeIsometries.shift N r z.1) + M6.Physical.weight N (M6.RecipeIsometries.shift N s z.2) = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  have h (t : ZMod N) (a : M6.RecipeIsometries.Block N) : M6.Physical.weight N (M6.RecipeIsometries.shift N t a) = M6.Physical.weight N a := by
    have hf : M6.RecipeIsometries.shift N t a = fun i => a ((Equiv.addRight (-t)) i) := by
      funext i
      exact congrArg a (sub_eq_add_neg i t)
    rw [hf]
    exact M6.RecipeIsometries.permutation_weight N (Equiv.addRight (-t)) a
  exact congrArg₂ (fun a b : ℕ => a + b) (h r z.1) (h s z.2)
