import FrozenTarget_0ee4f54bc85b27a1
theorem M7.Action.act_inverse : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.inverse g) (M7.Action.act g c) = c
  intro N inst g c
  rw [← M7.Action.act_compose N (M7.Action.inverse g) g c,
    M7.Action.left_inverse N g, M7.Action.act_identity N c]
