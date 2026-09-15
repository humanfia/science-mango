import M7FinalResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → M7.FinalResources.distanceWork N w E ≤ 50000*N^3 * (∑ i : Fin (M7.GeneratedFamily.size N w E), 4^(M6.ActualTransfer.span (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2))) ∧ ∀ i : Fin (M7.GeneratedFamily.size N w E), M6.ActualTransfer.actualSolveStorage N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) ≤ 16384*N^2*2^(M6.ActualTransfer.span (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2))
