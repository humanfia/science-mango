import FrozenTarget_8c5dbeabdea80b63
theorem M8.TaggedStore.write_layout : QuantumHarnessFrozenTarget := by
  change ∀ (key : M8.TaggedStore.Tag) (bit : Bool) (s : M8.TaggedStore.Store), _
  intro key bit s
  induction s with
  | nil =>
      simp [M8.TaggedStore.write, M8.TaggedStore.tapeBits]
  | cons r rs ih =>
      simp only [M8.TaggedStore.write]
      split
      · simp [M8.TaggedStore.tapeBits, M8.TaggedStore.recordBits]
      · constructor
        · simpa using congrArg (List.cons r.1) ih.1
        · change (M8.TaggedStore.recordBits r ++ M8.TaggedStore.tapeBits (M8.TaggedStore.write key bit rs).1).length = (M8.TaggedStore.recordBits r ++ M8.TaggedStore.tapeBits rs).length
          simpa only [List.length_append] using congrArg (fun n : ℕ => (M8.TaggedStore.recordBits r).length + n) ih.2
