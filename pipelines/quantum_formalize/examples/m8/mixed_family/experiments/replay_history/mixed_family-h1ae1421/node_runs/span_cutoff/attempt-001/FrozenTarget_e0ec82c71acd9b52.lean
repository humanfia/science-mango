import M8MixedFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Anchor.span (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N
