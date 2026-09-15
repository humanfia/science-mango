import M7CompactCorrectness


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (p : List Bool), M7.CompactGeneration.residual w E bases p = M7.RecoveryInstance.count w E bases p
