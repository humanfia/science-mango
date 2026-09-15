import M7DescentTrace


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), M7.DescentTrace.endpoint p (M7.DescentTrace.trace c p n) = M5.BinaryRecovery.recover c p n
