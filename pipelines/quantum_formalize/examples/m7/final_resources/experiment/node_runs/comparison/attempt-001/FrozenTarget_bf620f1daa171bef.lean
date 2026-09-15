import M7FinalResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ q : M7.DefaultQuery.Query, M7.FinalResources.comparisonCharge q (M7.GeneratedFamily.family N w E) ≤ 2 * ((M7.GeneratedFamily.size N w E) * (2*Nat.totient N*N^2))^2 * (q.objectives.length+1) * M7.FinalResources.objectiveBits q (M7.GeneratedFamily.family N w E)
