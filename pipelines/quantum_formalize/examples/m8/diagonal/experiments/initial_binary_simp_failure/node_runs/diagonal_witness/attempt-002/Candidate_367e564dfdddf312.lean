import FrozenTarget_367e564dfdddf312
theorem M8.Diagonal.diagonal_witness : QuantumHarnessFrozenTarget := by
  intro N inst p hp
  classical
  constructor
  · apply (M6.Spaces.logical_words_iff N p p _).2
    constructor
    · rw [M6.Flatten.flatten_left]
      funext i
      change M6.Physical.conv N p (M6.Physical.delta N 0) i + M6.Physical.conv N p (M6.Physical.delta N 0) i = 0
      have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
      exact htwo _
    · rintro ⟨h, he⟩
      apply hp
      refine ⟨h, ?_⟩
      have hh := congrArg (fun v => (M6.Flatten.unflatten N v).1) he
      simpa only [M6.Flatten.flatten_left, M6.Physical.boundary] using hh
  · rw [M6.Flatten.flatten_weight]
    norm_num [M6.Physical.wordWeight, M8.Diagonal.delta_weight]
