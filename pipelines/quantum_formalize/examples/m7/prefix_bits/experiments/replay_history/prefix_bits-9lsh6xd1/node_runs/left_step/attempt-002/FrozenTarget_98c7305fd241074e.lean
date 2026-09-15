import M7PrefixBits


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (p : List Bool) (bit : Bool), p.length < N-1 → let j := p.length+1; j ∈ M7.PrefixBits.WA N p ∧ M7.PrefixBits.A N (p ++ [bit]) = (if bit then insert j (M7.PrefixBits.A N p) else M7.PrefixBits.A N p) ∧ M7.PrefixBits.B N (p ++ [bit]) = M7.PrefixBits.B N p ∧ M7.PrefixBits.WA N (p ++ [bit]) = (M7.PrefixBits.WA N p).erase j ∧ M7.PrefixBits.WB N (p ++ [bit]) = M7.PrefixBits.WB N p
