import FrozenTarget_a2663b7e908e28cb
theorem M6.Character.sign_add : QuantumHarnessFrozenTarget := by
  change ∀ (a b : ZMod 2), M6.Character.sign (a + b) = M6.Character.sign a * M6.Character.sign b
  intro a b
  fin_cases a <;> fin_cases b <;> norm_num [M6.Character.sign]
