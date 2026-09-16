import M8CoverageFoundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (H : AddSubgroup (ZMod N)), M8.CoverageFoundation.InCoset A H → M8.CoverageFoundation.direction A ≤ H
