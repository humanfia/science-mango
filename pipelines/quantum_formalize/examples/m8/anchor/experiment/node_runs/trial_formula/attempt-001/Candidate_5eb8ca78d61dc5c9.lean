import FrozenTarget_5eb8ca78d61dc5c9
theorem M8.Anchor.trial_formula : QuantumHarnessFrozenTarget := by
  intro N inst c e u a b
  cases e <;> simp [M8.Anchor.trial, M8.Anchor.record, M8.Anchor.left, M8.Anchor.right, M7.Action.act, M7.Action.affine, mul_sub, sub_eq_add_neg]
