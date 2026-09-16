import FrozenTarget_e71a97b99ea84a13
theorem M8.TaggedStore.packed_layout : QuantumHarnessFrozenTarget := by
  change ∀ (start : ℕ) (mem : List Bool), (M8.TaggedStore.packFrom start mem).length = mem.length ∧ (∀ r ∈ M8.TaggedStore.packFrom start mem, r.1.length ≤ (start + mem.length).size) ∧ (M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom start mem)).length ≤ mem.length * (2 * (start + mem.length).size + 2)
  have hrecord : ∀ (tag : List Bool) (bit : Bool), (M8.TaggedStore.recordBits (tag, bit)).length = 2 * tag.length + 2 := by
    intro tag bit
    induction tag with
    | nil => simp [M8.TaggedStore.recordBits]
    | cons a tag ih =>
      simp only [M8.TaggedStore.recordBits, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
      omega
  intro start mem
  induction mem generalizing start with
  | nil => simp [M8.TaggedStore.packFrom, M8.TaggedStore.tapeBits]
  | cons b bs ih =>
    rcases ih (start + 1) with ⟨hlen, htags, htape⟩
    have he : start + (bs.length + 1) = (start + 1) + bs.length := by omega
    have hs : start.size ≤ (start + (bs.length + 1)).size := Nat.size_le_size (by omega)
    constructor
    · simpa only [M8.TaggedStore.packFrom, List.length_cons] using congrArg Nat.succ hlen
    constructor
    · intro r hr
      simp only [M8.TaggedStore.packFrom, List.mem_cons] at hr
      rcases hr with hr | hr
      · subst r
        change (M8.TaggedStore.address start).length ≤ (start + (bs.length + 1)).size
        rw [M8.TaggedStore.address_representation.2]
        exact hs
      · simpa only [List.length_cons, he] using htags r hr
    · change (M8.TaggedStore.recordBits (M8.TaggedStore.address start, b) ++ M8.TaggedStore.tapeBits (M8.TaggedStore.packFrom (start + 1) bs)).length ≤ (bs.length + 1) * (2 * (start + (bs.length + 1)).size + 2)
      rw [List.length_append, hrecord, M8.TaggedStore.address_representation.2]
      rw [← he] at htape
      nlinarith
