import FrozenTarget_6af80d5573ec1a8d
theorem M7.Action.right_inverse : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose g (M7.Action.inverse g) = M7.Action.identity N
  intro N inst g
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M7.Action.compose, M7.Action.inverse, M7.Action.identity, mul_neg, ← mul_assoc]
