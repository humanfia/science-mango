import M7CompactStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M7.RecipeSignature.signature c).natDegree ≤ N ∧ M7.ActualOrbit.stabilizerCount c < 2^(1+3*N)
