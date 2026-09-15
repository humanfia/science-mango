import M7GeneratedLabels


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ (i : Fin (M7.GeneratedFamily.size N w E)) (g : M7.Action.Record N), (M7.DefaultQuery.dimension (M7.Action.act g (M7.GeneratedFamily.family N w E i)), M7.DefaultQuery.distance (M7.Action.act g (M7.GeneratedFamily.family N w E i))) = M7.QualityTable.cache (M7.GeneratedFamily.family N w E i)
