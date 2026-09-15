import FrozenTarget_437f8a493a4b104d
theorem M7.Action.left_inverse : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.inverse g) g = M7.Action.identity N
  intro N inst g
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M7.Action.compose, M7.Action.inverse, M7.Action.identity]
