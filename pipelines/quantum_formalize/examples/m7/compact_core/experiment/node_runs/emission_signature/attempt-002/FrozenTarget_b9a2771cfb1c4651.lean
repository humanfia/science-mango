import M7CompactGeneration


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), (M7.CompactGeneration.emission w E bases).leafSignature = M7.RecipeSignature.signature (M7.CompactGeneration.emission w E bases).leaf ∧ (M7.CompactGeneration.emission w E bases).representativeSignature = M7.SignatureTau.sourceTau (M7.CompactGeneration.emission w E bases).action.unit (M7.CompactGeneration.emission w E bases).leafSignature
