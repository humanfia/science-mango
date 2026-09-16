import FrozenTarget_40b2290adc094571
theorem M8.Anchor.trial_formula : QuantumHarnessFrozenTarget := by
  intro N inst c e u a b
  cases e <;> simp [M8.Anchor.trial, M8.Anchor.record, M8.Anchor.left, M8.Anchor.right, M7.Action.act] <;> constructor <;> congr 1 <;> funext i <;> dsimp [M7.Action.affine] <;> ring
