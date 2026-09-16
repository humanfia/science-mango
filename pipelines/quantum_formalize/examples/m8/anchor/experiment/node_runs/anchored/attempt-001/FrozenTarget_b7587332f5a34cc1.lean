import M8Anchor


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b → M8.Anchor.Anchored (M8.Anchor.trial c e u a b)
