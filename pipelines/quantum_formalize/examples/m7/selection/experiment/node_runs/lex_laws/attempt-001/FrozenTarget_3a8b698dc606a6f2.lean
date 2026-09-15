import M7Selection


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.lex a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.lex a b → M7.Selection.lex b c → M7.Selection.lex a c)
