import M7DescentTrace


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), p.IsPrefix (M5.BinaryRecovery.recover c p n)
