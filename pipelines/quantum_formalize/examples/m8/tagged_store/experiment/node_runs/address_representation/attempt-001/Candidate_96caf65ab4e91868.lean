import FrozenTarget_96caf65ab4e91868
theorem M8.TaggedStore.address_representation : QuantumHarnessFrozenTarget := by
  change Function.Injective M8.TaggedStore.address ∧ ∀ i : ℕ, (M8.TaggedStore.address i).length = i.size
  constructor
  · intro m n h
    change m.bits = n.bits at h
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_eq_inth, h]
  · intro i
    change i.bits.length = i.size
    exact (Nat.size_eq_bits_len i).symm
