import M5OriginalRootReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.ResidueRecoveryClause w F
