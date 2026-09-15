import M7CompactGeneration


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.DescentTrace.check (M7.CompactGeneration.residual w E bases) [] (M7.CompactGeneration.emission w E bases).path = (true, 2 * M7.PrefixBits.depth N)
