import M5OriginalSpec


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.PeriodClause F ∧ M5.Final.OrderClause w F ∧ M5.Final.LowerClause w F ∧ M5.Final.WeightOneClause F
