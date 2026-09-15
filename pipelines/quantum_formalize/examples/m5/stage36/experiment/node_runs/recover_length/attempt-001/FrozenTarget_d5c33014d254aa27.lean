import M5BinaryRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M5.BinaryRecovery.recover c p n).length = p.length + n
