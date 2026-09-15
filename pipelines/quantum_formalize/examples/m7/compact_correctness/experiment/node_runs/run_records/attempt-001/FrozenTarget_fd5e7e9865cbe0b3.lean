import M7CompactCorrectness


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), ∀ e ∈ (M7.CompactGeneration.run w E fuel bases root).emitted, M7.Action.act e.action e.leaf = e.representative ∧ M7.Action.act (M7.Action.inverse e.action) e.representative = e.leaf ∧ e.leafSignature = M7.RecipeSignature.signature e.leaf ∧ e.representativeSignature = M7.RecipeSignature.signature e.representative ∧ e.stabilizer = M7.ActualFactorized.stabilizerNumerator e.representative ∧ 0 < e.stabilizer
