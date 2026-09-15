import FrozenTarget_eafee8cfdd44ada6
theorem M5.Packing.packed_support_anchor : QuantumHarnessFrozenTarget := by
  intro w T r hw h
  classical
  unfold M5.Packing.packedSupport
  refine Finset.mem_image.mpr ⟨⟨0, hw⟩, Finset.mem_univ _, ?_⟩
  simp [M5.Packing.packedValue, M5.Packing.occurrenceTag, M5.Packing.priorOccurrences, h]
