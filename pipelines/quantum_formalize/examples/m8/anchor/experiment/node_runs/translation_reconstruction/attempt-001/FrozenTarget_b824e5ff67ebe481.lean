import M8Anchor


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (g : M7.Action.Record N), M8.Anchor.Anchored (M7.Action.act g c) → ∃ a b : ZMod N, M8.Anchor.Eligible c g.exchange a b ∧ M8.Anchor.record g.exchange g.unit a b = g
