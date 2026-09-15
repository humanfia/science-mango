import M7PrefixSector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E H : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint E H → M7.PrefixSector.count N w (E ∪ H) A B WA WB = M7.PrefixSector.count N w E A B WA WB + M7.PrefixSector.count N w H A B WA WB
