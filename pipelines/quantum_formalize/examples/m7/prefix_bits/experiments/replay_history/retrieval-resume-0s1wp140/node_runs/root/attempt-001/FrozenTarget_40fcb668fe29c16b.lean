import M7PrefixBits


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → M7.PrefixBits.A N [] = {0} ∧ M7.PrefixBits.B N [] = {0} ∧ M7.PrefixBits.WA N [] = Finset.range N \ {0} ∧ M7.PrefixBits.WB N [] = Finset.range N \ {0}
