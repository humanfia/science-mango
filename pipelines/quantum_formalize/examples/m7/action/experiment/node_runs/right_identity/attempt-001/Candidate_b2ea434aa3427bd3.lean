import FrozenTarget_b2ea434aa3427bd3
theorem M7.Action.right_identity : QuantumHarnessFrozenTarget := by
  intro N inst g
  change M7.Action.compose g (M7.Action.identity N) = g
  rcases g with ⟨u, b, s, t⟩
  cases b <;> simp [M7.Action.compose, M7.Action.identity]
