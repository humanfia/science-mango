import M8MixedNonproduct


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 7 ≤ N → (M7.Supports.indicator (M8.MixedFamily.left N),M7.Supports.indicator (M8.MixedFamily.right N)) ∈ M8.MixedNonproduct.Cycles (M8.MixedFamily.recipe N) ∧ (0,0) ∈ M8.MixedNonproduct.Cycles (M8.MixedFamily.recipe N) ∧ (M7.Supports.indicator (M8.MixedFamily.left N),0) ∉ M8.MixedNonproduct.Cycles (M8.MixedFamily.recipe N)
