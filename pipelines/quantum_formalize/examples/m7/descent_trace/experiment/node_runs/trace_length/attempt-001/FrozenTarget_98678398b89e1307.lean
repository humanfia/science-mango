import M7DescentTrace


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.DescentTrace.trace c p n).length = n
