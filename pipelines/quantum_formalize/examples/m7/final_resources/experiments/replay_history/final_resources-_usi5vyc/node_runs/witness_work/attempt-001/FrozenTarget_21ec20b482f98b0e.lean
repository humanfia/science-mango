import M7FinalResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ (d k : Fin (M7.GeneratedFamily.size N w E) → ℕ) (v : Fin (M7.GeneratedFamily.size N w E) → M6.Pinned.Vector (2*N)), (∀ i, M6.ActualTransfer.solve N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) = some (d i,v i,k i)) → (∑ i : Fin (M7.GeneratedFamily.size N w E), M6.ActualTransfer.actualWitnessWork N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) (k i)) ≤ 200000*N^4 * (∑ i : Fin (M7.GeneratedFamily.size N w E), 4^(M6.ActualTransfer.span (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2)))
