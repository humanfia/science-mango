import M7CanonicalOuter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (e : Bool), ∃ i ∈ M7.CanonicalOuter.indices N, M7.CanonicalOuter.outerRecord i = (⟨u,e,0,0⟩ : M7.Action.Record N)
