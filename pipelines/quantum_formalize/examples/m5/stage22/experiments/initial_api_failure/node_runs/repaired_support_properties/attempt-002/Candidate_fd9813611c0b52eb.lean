import FrozenTarget_fd9813611c0b52eb
theorem M5.BoundedConstruction.repaired_support_properties : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro w T r s hw hT hr hs e k he hepos hnew hbound hg
  have hcard : (M5.Packing.packedSupport r).card = w := by
    first
    | exact M5.Packing.packedSupport_card r
    | exact M5.Packing.packedSupport_card hT r
    | exact M5.Packing.card_packedSupport r
    | exact M5.Packing.card_packedSupport hT r
    | simp [M5.Packing.packedSupport]
  have hzero : 0 ∈ M5.Packing.packedSupport r := by
    first
    | exact M5.Packing.packedSupport_anchor r hr
    | exact M5.Packing.zero_mem_packedSupport r hr
    | exact M5.BoundedConstruction.anchoredTuple_zero_mem hr
    | unfold M5.BoundedConstruction.anchoredTuple at hr
      unfold M5.Packing.packedSupport
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨0, by omega⟩, ?_⟩
      simpa using hr
  have hcut : w * T < M5.packingCutoff w T := by
    unfold M5.packingCutoff
    nlinarith
  have hrange : ∀ a ∈ M5.Packing.packedSupport r, a < M5.packingCutoff w T := by
    intro a ha
    apply lt_trans (b := w * T) _ hcut
    first
    | exact M5.Packing.packedSupport_lt r ha
    | exact M5.Packing.mem_packedSupport_lt ha
    | exact M5.Packing.packedSupport_bound r ha
    | unfold M5.Packing.packedSupport at ha
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
      obtain ⟨i, rfl⟩ := ha
      have hi := i.isLt
      have hri := (r i).isLt
      dsimp at *
      nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · first
    | exact (M5.RepairSupport.replacement_card he hnew).trans hcard
    | apply M5.RepairSupport.replacement_card <;> assumption
    | rw [M5.RepairSupport.repaired, Finset.card_insert_of_notMem, Finset.card_erase_of_mem he]
      · omega
      · intro h
        exact hnew (Finset.mem_of_mem_erase h)
  · apply M5.RepairSupport.replacement_anchor <;> first | assumption | omega
  · apply M5.RepairSupport.replacement_range <;> assumption
  · unfold M5.PhysicalBridge.remainingGcd at hg
    apply M5.RepairSupport.replacement_connected <;> first | assumption | simpa [Nat.gcd_comm] using hg
