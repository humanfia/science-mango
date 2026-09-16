import M8TaggedStore

theorem M8.TaggedStore.address_representation : Function.Injective M8.TaggedStore.address ∧ ∀ i : ℕ, (M8.TaggedStore.address i).length = i.size := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (start : ℕ) (mem : List Bool), (M8.TaggedStore.packFrom start mem).length = mem.length ∧ (∀ r ∈ M8.TaggedStore.packFrom start mem, r.1.length ≤ (start+mem.length).size) ∧ (M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom start mem)).length ≤ mem.length*(2*(start+mem.length).size+2)
