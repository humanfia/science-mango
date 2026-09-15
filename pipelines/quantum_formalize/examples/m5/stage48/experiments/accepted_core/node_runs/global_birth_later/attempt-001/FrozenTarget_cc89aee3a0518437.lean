import M5OriginalSpec


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → M5.Final.GlobalClause w F ∧ M5.Final.ProgressionClause w F ∧ M5.Final.BirthClause w F ∧ M5.Final.LaterClause w F
