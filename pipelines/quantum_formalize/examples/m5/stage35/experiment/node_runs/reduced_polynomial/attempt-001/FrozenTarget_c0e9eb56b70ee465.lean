import M5ResidueNecessity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (hT : 0 < T) (u : Fin w → ℕ), Function.Injective u → AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (Finset.univ.image u)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple (M5.ResidueNecessity.reduceTuple T hT u))
