import M8Coverage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Coverage.Recognized (M8.MixedFamily.recipe N) ∧ M8.PhysicalBridge.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.MixedFamily.recipe N))) ∧ (∀ g : M7.Action.Record N, ¬ M8.MixedNonproduct.Product (M7.Action.act g (M8.MixedFamily.recipe N)))
