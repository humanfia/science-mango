import M7CompactGeneration


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.Action.act (M7.CompactGeneration.emission w E bases).action (M7.CompactGeneration.emission w E bases).leaf = (M7.CompactGeneration.emission w E bases).representative ∧ M7.Action.act (M7.Action.inverse (M7.CompactGeneration.emission w E bases).action) (M7.CompactGeneration.emission w E bases).representative = (M7.CompactGeneration.emission w E bases).leaf
