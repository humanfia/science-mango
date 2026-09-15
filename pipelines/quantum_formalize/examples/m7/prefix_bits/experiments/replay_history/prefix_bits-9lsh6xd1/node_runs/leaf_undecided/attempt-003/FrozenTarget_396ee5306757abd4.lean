import M7PrefixBits


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ p : List Bool, p.length = M7.PrefixBits.depth N → M7.PrefixBits.WA N p = ∅ ∧ M7.PrefixBits.WB N p = ∅
