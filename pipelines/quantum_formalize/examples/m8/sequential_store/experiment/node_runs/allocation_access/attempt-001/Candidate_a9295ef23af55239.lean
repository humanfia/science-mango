import FrozenTarget_a9295ef23af55239
theorem M8.SequentialStore.allocation_access : QuantumHarnessFrozenTarget := by
  intro N inst mem hmem i bit
  have layout := M8.TaggedStore.packed_layout 0 mem
  have hkey : (M8.TaggedStore.address i.val).length ≤ (M8.SequentialStore.slots N).size := by
    rw [M8.TaggedStore.address_representation.2]
    exact Nat.size_le_size (Nat.le_of_lt i.isLt)
  have htags : ∀ r ∈ M8.TaggedStore.packFrom 0 mem, r.1.length ≤ (M8.SequentialStore.slots N).size := by
    simpa only [Nat.zero_add, hmem] using layout.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using M8.TaggedStore.indexed_read 0 i.val mem
  · simpa only [Nat.zero_add] using M8.TaggedStore.indexed_write 0 i.val bit mem
  · simpa only [M8.SequentialStore.accessCharge, M8.SequentialStore.addressBits, layout.1, hmem] using
      M8.TaggedStore.read_work (M8.SequentialStore.slots N).size (M8.TaggedStore.address i.val) (M8.TaggedStore.packFrom 0 mem) hkey htags
  · simpa only [M8.SequentialStore.accessCharge, M8.SequentialStore.addressBits, layout.1, hmem] using
      M8.TaggedStore.write_work (M8.SequentialStore.slots N).size (M8.TaggedStore.address i.val) bit (M8.TaggedStore.packFrom 0 mem) hkey htags
