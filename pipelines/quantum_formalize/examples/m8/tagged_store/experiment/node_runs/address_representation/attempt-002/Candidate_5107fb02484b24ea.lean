import FrozenTarget_5107fb02484b24ea
theorem M8.TaggedStore.address_representation : QuantumHarnessFrozenTarget := by
  change Function.Injective M8.TaggedStore.address ∧ ∀ i : ℕ, (M8.TaggedStore.address i).length = i.size
  constructor
  · intro a b h
    change a.bits = b.bits at h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]
  · intro i
    change i.bits.length = i.size
    exact Nat.size_eq_bits_len i
