import M8TaggedStore


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (key : M8.TaggedStore.Tag) (bit : Bool) (s : M8.TaggedStore.Store), ((M8.TaggedStore.write key bit s).1.map Prod.fst) = s.map Prod.fst ∧ (M8.TaggedStore.tapeBits (M8.TaggedStore.write key bit s).1).length = (M8.TaggedStore.tapeBits s).length
