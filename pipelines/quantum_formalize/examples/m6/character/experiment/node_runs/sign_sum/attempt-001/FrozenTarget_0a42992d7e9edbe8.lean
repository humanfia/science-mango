import M6Character

theorem M6.Character.sign_add : ∀ (a b : ZMod 2), M6.Character.sign (a+b) = M6.Character.sign a * M6.Character.sign b := by
  change ∀ (a b : ZMod 2), M6.Character.sign (a + b) = M6.Character.sign a * M6.Character.sign b
  intro a b
  fin_cases a <;> fin_cases b <;> decide
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (f : Fin m → ZMod 2), M6.Character.sign (∑ i, f i) = ∏ i, M6.Character.sign (f i)
