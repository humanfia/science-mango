import M7CanonicalOuter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.normalizePair (M7.Action.act g c) = M7.CanonicalOuter.normalizePair (M7.Action.act (⟨g.unit,g.exchange,0,0⟩ : M7.Action.Record N) c)
