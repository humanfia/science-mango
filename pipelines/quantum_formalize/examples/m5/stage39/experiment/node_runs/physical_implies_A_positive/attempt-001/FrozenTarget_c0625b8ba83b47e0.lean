import M5GlobalCriterionReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (S U : Finset ℕ), 0 < w → F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F S U → 0 < M5.ResidueCount.A w F
