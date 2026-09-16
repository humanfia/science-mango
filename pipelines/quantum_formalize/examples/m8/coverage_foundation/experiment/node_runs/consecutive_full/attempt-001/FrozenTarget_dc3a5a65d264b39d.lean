import M8CoverageFoundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (a : ZMod N), a ∈ A → a+1 ∈ A → M8.CoverageFoundation.FullDirection A
