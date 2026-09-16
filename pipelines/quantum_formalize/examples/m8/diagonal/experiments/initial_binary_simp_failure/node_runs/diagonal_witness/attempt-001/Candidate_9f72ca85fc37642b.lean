import FrozenTarget_9f72ca85fc37642b
theorem M8.Diagonal.diagonal_witness : QuantumHarnessFrozenTarget := by
  intro N inst p hp
  classical
  constructor
  · apply (M6.Spaces.logical_words_iff N p p _).2
    constructor
    · rw [M6.Flatten.flatten_left]
      funext i
      change M6.Physical.conv N p (M6.Physical.delta N 0) i + M6.Physical.conv N p (M6.Physical.delta N 0) i = 0
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [← two_mul, htwo, zero_mul]
    · rintro ⟨h, hh⟩
      have he := congrArg (M6.Flatten.unflatten N) hh
      rw [M6.Flatten.flatten_left, M6.Flatten.flatten_left] at he
      have hf := congrArg Prod.fst he
      apply hp
      refine ⟨h, ?_⟩
      exact hf
  · rw [M6.Flatten.flatten_weight]
    change M6.Physical.weight N (M6.Physical.delta N 0) + M6.Physical.weight N (M6.Physical.delta N 0) = 2
    rw [M8.Diagonal.delta_weight]
    norm_num
