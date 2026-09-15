import M7CompactGeneration


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), 0 < (M7.CompactGeneration.emission w E bases).stabilizer ∧ (M7.CompactGeneration.emission w E bases).stabilizer = M7.ActualOrbit.stabilizerCount (M7.CompactGeneration.emission w E bases).representative
