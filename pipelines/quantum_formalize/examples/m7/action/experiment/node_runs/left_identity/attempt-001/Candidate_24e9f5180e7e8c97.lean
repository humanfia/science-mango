import FrozenTarget_24e9f5180e7e8c97
theorem M7.Action.left_identity : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.identity N) g = g
  intro N inst g
  rcases g with ⟨u, e, l, r⟩
  cases e <;> simp [M7.Action.compose, M7.Action.identity]
