import M8Anchor


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.trial c e u a b = ((M8.Anchor.left c e).image (fun i => (u : ZMod N)*(i-a)), (M8.Anchor.right c e).image (fun i => (u : ZMod N)*(i-b)))
