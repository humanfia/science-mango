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

theorem M8.TaggedStore.comparison_exact : ∀ a b : M8.TaggedStore.Tag, (M8.TaggedStore.compare a b).1 = decide (a=b) ∧ (M8.TaggedStore.compare a b).2 ≤ a.length+1 := by
  change ∀ a b : M8.TaggedStore.Tag, (M8.TaggedStore.compare a b).1 = decide (a = b) ∧ (M8.TaggedStore.compare a b).2 ≤ a.length + 1
  intro a
  induction a with
  | nil =>
      intro b
      cases b <;> simp [M8.TaggedStore.compare]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [M8.TaggedStore.compare]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simpa [M8.TaggedStore.compare] using ih ys
          · simp [M8.TaggedStore.compare, h]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (start i : ℕ) (mem : List Bool), (M8.TaggedStore.read (M8.TaggedStore.address (start+i)) (M8.TaggedStore.packFrom start mem)).1 = mem[i]?
