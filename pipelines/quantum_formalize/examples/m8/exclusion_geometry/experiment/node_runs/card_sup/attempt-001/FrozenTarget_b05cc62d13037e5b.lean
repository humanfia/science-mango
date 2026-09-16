import M8ExclusionGeometry


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ B : Finset (ZMod N), B.card ≤ B.sup ZMod.val + 1
