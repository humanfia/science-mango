import M8P4Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.Anchor.span (M8.P4Family.recipe N) ≤ M8.Cutoff.limit N
