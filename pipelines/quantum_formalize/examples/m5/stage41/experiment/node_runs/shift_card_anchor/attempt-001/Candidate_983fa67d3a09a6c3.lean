import FrozenTarget_983fa67d3a09a6c3
theorem M5.Translation.shift_card_anchor : QuantumHarnessFrozenTarget := by
  intro N inst S c hc
  classical
  unfold M5.Translation.shift
  constructor
  · apply Finset.card_image_iff.mpr
    intro a ha b hb h
    dsimp at h
    first
    | exact add_right_cancel h
    | exact add_left_cancel h
  · apply Finset.mem_image.mpr
    exact ⟨c, hc, by simp⟩
