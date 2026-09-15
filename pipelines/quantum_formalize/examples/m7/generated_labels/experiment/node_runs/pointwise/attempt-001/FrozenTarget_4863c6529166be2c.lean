import M7GeneratedLabels


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ i : Fin (M7.GeneratedFamily.size N w E), M6.Final.PointwiseCorrect N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2)
