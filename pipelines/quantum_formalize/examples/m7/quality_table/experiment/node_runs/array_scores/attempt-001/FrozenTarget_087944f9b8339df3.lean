import M7QualityTable


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (g : M7.Action.Record N), (M7.QualityTable.leftTable c (g.unit,g.exchange)).size = N ∧ (M7.QualityTable.rightTable c (g.unit,g.exchange)).size = N ∧ M7.QualityTable.placedScores c g = (M7.DefaultQuery.locality (M7.Action.act g c), M7.DefaultQuery.radius (M7.Action.act g c))
