import M8P3Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.Anchor.span (M8.P3Family.recipe N) ≤ M8.Cutoff.limit N
