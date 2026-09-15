import FrozenTarget_cf37503427874fb9
theorem M6.Character.sign_add : QuantumHarnessFrozenTarget := by
  change ∀ (a b : ZMod 2), M6.Character.sign (a + b) = M6.Character.sign a * M6.Character.sign b
  intro a b
  fin_cases a <;> fin_cases b <;> decide
