import M7StreamingIndices


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, ∃ (u : Fin (Fintype.card ((ZMod N)ˣ))) (e : Fin 2) (s t : Fin N), M7.StreamingIndices.decodeRecord N u e s t = g
