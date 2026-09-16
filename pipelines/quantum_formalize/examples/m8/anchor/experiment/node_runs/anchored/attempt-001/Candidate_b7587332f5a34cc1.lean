import FrozenTarget_b7587332f5a34cc1
theorem M8.Anchor.anchored : QuantumHarnessFrozenTarget := by
  intro N _ c e u a b h
  cases e <;> simp only [M8.Anchor.Eligible, M8.Anchor.left, M8.Anchor.right, Bool.false_eq_true, if_false, if_true] at h
  all_goals
    rcases h with ⟨ha, hb⟩
    dsimp [M8.Anchor.Anchored, M8.Anchor.trial, M8.Anchor.record, M7.Action.act]
    constructor
  all_goals
    first
    | exact Finset.mem_image.mpr ⟨a, ha, by simp [M7.Action.affine]⟩
    | exact Finset.mem_image.mpr ⟨b, hb, by simp [M7.Action.affine]⟩
