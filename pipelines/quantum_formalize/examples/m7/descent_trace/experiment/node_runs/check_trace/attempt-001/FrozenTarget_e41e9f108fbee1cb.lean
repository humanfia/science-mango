import M7DescentTrace


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), M7.DescentTrace.check c p (M7.DescentTrace.trace c p n) = (true,2*n)
