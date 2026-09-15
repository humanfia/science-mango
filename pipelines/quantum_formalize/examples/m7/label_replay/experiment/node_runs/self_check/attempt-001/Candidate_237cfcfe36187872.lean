import FrozenTarget_237cfcfe36187872
theorem M7.LabelReplay.self_check : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M7.LabelReplay.check c (M7.LabelReplay.expected c) = true
  intro N _ c
  classical
  simp [M7.LabelReplay.check, M7.LabelReplay.expected]
