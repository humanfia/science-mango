import FrozenTarget_03af5dcaa0baedde
theorem M8.Anchor.inverse_trial : QuantumHarnessFrozenTarget := by
  intro N inst c e u a b
  exact M7.Action.act_inverse N (M8.Anchor.record e u a b) c
