import M8Anchor


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (e : Bool) (u : (ZMod N)ˣ) (a b a1 b1 : ZMod N), M8.Anchor.record e u a b = M8.Anchor.record e u a1 b1 → a = a1 ∧ b = b1
