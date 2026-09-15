import FrozenTarget_8604f9db9e66451e
theorem M7.Action.associative : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ g h k : M7.Action.Record N, M7.Action.compose (M7.Action.compose g h) k = M7.Action.compose g (M7.Action.compose h k)
  intro N inst g h k
  rcases g with ⟨u, e, a, b⟩
  rcases h with ⟨v, f, c, d⟩
  rcases k with ⟨w, q, s, t⟩
  cases e <;> cases f <;> cases q <;>
    simp [M7.Action.compose, mul_add, mul_assoc, add_assoc]
