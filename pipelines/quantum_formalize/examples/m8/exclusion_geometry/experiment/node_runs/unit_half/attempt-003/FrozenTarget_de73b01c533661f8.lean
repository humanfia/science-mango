import M8ExclusionGeometry


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (u : (ZMod N)ˣ), N = 2*h → (u : ZMod N) * (h : ZMod N) = (h : ZMod N)
