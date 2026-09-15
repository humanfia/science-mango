import M7PrefixSector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B WA WB → 0 ≤ M7.PrefixSector.count N w E A B WA WB
