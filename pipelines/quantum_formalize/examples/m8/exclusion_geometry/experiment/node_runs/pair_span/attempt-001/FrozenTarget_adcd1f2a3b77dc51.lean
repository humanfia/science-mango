import M8ExclusionGeometry


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (B : Finset (ZMod N)), N = 2*h → M8.ExclusionGeometry.Antipodal h B → h ≤ B.sup ZMod.val
