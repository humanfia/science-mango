import M7CanonicalOuter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], Function.Injective (M7.CanonicalOuter.pairKey (N := N))
