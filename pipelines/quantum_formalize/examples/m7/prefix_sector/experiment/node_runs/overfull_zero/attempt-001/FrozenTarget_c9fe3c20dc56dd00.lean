import M7PrefixSector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), (w < A.card ∨ w < B.card) → M7.PrefixSector.count N w E A B WA WB = 0
