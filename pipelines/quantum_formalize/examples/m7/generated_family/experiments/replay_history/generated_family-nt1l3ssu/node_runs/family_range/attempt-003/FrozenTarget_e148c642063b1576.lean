import M7GeneratedFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ b : M7.Action.Recipe N, b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases ↔ ∃ i : Fin (M7.GeneratedFamily.size N w E), M7.GeneratedFamily.family N w E i = b
