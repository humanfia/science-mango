import M8TaggedStore


def QuantumHarnessFrozenTarget : Prop :=
  Function.Injective M8.TaggedStore.address ∧ ∀ i : ℕ, (M8.TaggedStore.address i).length = i.size
