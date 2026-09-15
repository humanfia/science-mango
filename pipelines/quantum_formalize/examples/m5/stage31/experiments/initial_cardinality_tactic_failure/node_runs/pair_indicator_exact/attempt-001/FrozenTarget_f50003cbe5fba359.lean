import M5ResidueCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T k : ℕ) (F : M5.BinaryPolynomial) (a b : Fin k → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.pairIndicator F a b = (@ite ℤ (M5.ResidueCount.feasible F a b) (Classical.propDecidable _) 1 0)
