import M7OverfullBoundary


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N], 0 < w → M7.CompactGeneration.residual (N := N) w ∅ ∅ [] = 0
