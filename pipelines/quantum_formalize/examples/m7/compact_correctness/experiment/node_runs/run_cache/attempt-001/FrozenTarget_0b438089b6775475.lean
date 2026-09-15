import M7CompactCorrectness


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), root = M7.CompactGeneration.residual w E bases [] → (M7.CompactGeneration.run w E fuel bases root).finalResidual = M7.CompactGeneration.residual w E (M7.CompactGeneration.run w E fuel bases root).finalBases []
