import M7PrefixBits


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ p : List Bool, M7.PrefixCompleted.Base N (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p)
