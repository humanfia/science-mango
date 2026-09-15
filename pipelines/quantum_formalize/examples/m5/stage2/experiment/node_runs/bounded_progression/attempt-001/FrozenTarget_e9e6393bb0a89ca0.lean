import M5Lift


def QuantumHarnessFrozenTarget : Prop :=
  ∀ T E L : ℕ, 0 < E → T < L → ∃ j : ℕ, L ≤ T + j * E ∧ T + j * E < L + E
