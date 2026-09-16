import M8TaggedStore


def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b : M8.TaggedStore.Tag, (M8.TaggedStore.compare a b).1 = decide (a=b) ∧ (M8.TaggedStore.compare a b).2 ≤ a.length+1
