import FrozenTarget_969d55bcfda84abe
theorem M5.Packing.packed_support_anchor : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (hw : 0 < w), (r ⟨0, hw⟩).val = 0 → 0 ∈ M5.Packing.packedSupport r
  intro w T r hw h
  unfold M5.Packing.packedSupport
  apply Finset.mem_image.mpr
  refine ⟨⟨0, hw⟩, Finset.mem_univ _, ?_⟩
  simp [M5.Packing.packedValue, M5.Packing.occurrenceTag, M5.Packing.priorOccurrences, Fin.lt_def, h]
