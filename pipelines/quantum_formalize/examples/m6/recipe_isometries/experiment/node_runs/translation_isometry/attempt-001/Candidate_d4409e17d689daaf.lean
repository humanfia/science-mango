import FrozenTarget_d4409e17d689daaf
theorem M6.RecipeIsometries.translation_isometry : QuantumHarnessFrozenTarget := by
  intro N inst a b r s
  have hinv (t u : ZMod N) (z : M6.RecipeIsometries.Word N) :
      M6.RecipeIsometries.translateWord N (-t) (-u)
        (M6.RecipeIsometries.translateWord N t u z) = z := by
    apply Prod.ext
    · exact (M6.RecipeIsometries.shift_laws N t z.1).2.1
    · exact (M6.RecipeIsometries.shift_laws N u z.2).2.1
  refine M6.RecipeIsometries.lift_transport N a b
    (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b)
    (M6.RecipeIsometries.translateWord N r s) (fun h => h) ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro x y h
      have he := congrArg (M6.RecipeIsometries.translateWord N (-r) (-s)) h
      simpa only [hinv] using he
    · intro z
      refine ⟨M6.RecipeIsometries.translateWord N (-r) (-s) z, ?_⟩
      simpa only [neg_neg] using hinv (-r) (-s) z
  · intro h
    exact ⟨h, rfl⟩
  · intro h
    exact M6.RecipeIsometries.translated_boundary N r s a b h
  · intro z
    rw [M6.RecipeIsometries.translated_syndrome]
    exact (M6.RecipeIsometries.shift_laws N (r + s)
      (M6.Physical.syndrome N a b z)).2.2
  · exact M6.RecipeIsometries.translated_weight N r s
