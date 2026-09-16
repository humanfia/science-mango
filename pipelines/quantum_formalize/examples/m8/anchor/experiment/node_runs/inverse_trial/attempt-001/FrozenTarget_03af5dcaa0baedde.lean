import M8Anchor


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M7.Action.act (M7.Action.inverse (M8.Anchor.record e u a b)) (M8.Anchor.trial c e u a b) = c
