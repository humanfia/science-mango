import FrozenTarget_10de994e78aa3616
theorem M6.RecipeIsometries.lift_transport : QuantumHarnessFrozenTarget := by
  intro N inst a b a1 b1 P H hP hH hB hC hW
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro x y h
    have h' := congrArg (M6.Flatten.unflatten N) h
    simpa only [M6.Flatten.flatten_left] using h'
  have hu : Function.Injective (M6.Flatten.unflatten N) := by
    intro x y h
    have h' := congrArg (M6.Flatten.flatten N) h
    simpa only [M6.Flatten.flatten_right] using h'
  constructor
  · constructor
    · intro x y h
      apply hu
      apply hP.1
      apply hf
      exact h
    · intro v
      obtain ⟨z, hz⟩ := hP.2 (M6.Flatten.unflatten N v)
      refine ⟨M6.Flatten.flatten N z, ?_⟩
      simp only [M6.RecipeIsometries.lift, M6.Flatten.flatten_left, hz,
        M6.Flatten.flatten_right]
  · intro v
    constructor
    · rw [M6.Spaces.boundary_words_iff, M6.Spaces.boundary_words_iff]
      constructor
      · rintro ⟨k, hk⟩
        obtain ⟨h, rfl⟩ := hH k
        rw [hB h] at hk
        change M6.Flatten.flatten N (P (M6.Physical.boundary N a b h)) =
          M6.Flatten.flatten N (P (M6.Flatten.unflatten N v)) at hk
        have he := hP.1 (hf hk)
        refine ⟨h, ?_⟩
        exact (congrArg (M6.Flatten.flatten N) he).trans
          (M6.Flatten.flatten_right N v)
      · rintro ⟨h, hh⟩
        have he : M6.Physical.boundary N a b h = M6.Flatten.unflatten N v := by
          have he' := congrArg (M6.Flatten.unflatten N) hh
          simpa only [M6.Flatten.flatten_left] using he'
        refine ⟨H h, ?_⟩
        rw [hB h, he]
        rfl
    · constructor
      · simp only [M6.Spaces.cycle_words_iff, M6.RecipeIsometries.lift,
          M6.Flatten.flatten_left]
        exact hC (M6.Flatten.unflatten N v)
      · change M6.Pinned.weight
          (M6.Flatten.flatten N (P (M6.Flatten.unflatten N v))) =
          M6.Pinned.weight v
        rw [M6.Flatten.flatten_weight, hW]
        calc
          M6.Physical.wordWeight N (M6.Flatten.unflatten N v) =
              M6.Pinned.weight (M6.Flatten.flatten N (M6.Flatten.unflatten N v)) :=
            (M6.Flatten.flatten_weight N (M6.Flatten.unflatten N v)).symm
          _ = M6.Pinned.weight v := by rw [M6.Flatten.flatten_right]
