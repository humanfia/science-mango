import M7CompactGeneration


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), ∀ (fuel : ℕ) (root : ℤ), (M7.CompactGeneration.run w E fuel bases root).emitted.length ≤ fuel
