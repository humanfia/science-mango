import FrozenTarget_e6f7fe9e657034e2
theorem M7.Action.normal_form : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst g
  rcases g with ⟨u, b, s, t⟩
  cases b <;> simp [M7.Action.compose, M7.Action.translate, M7.Action.multiplier, M7.Action.exchange, M7.Action.identity]
