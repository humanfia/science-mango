import FrozenTarget_877f2f366dec11cd
theorem M5.BoundedConstruction.repaired_support_properties : QuantumHarnessFrozenTarget := by
    intro w T r s hw hT hr hs e k he hepos hnew hbound hg
    classical
    have hcard : (M5.Packing.packedSupport r).card = w :=
      M5.Packing.packed_support_card w T r
    have hzero : 0 ∈ M5.Packing.packedSupport r := by
      unfold M5.BoundedConstruction.anchoredTuple at hr
      first
      | solve | exact?
      | solve
          simp_all [M5.Packing.packedSupport, M5.Packing.packedValue,
            M5.Packing.occurrenceTag]
      | solve
          unfold M5.Packing.packedSupport
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          refine ⟨⟨0, by omega⟩, ?_⟩
          simp_all [M5.Packing.packedValue, M5.Packing.occurrenceTag]
    have hcut : w * T < M5.packingCutoff w T := by
      have hp : 0 < w * T := Nat.mul_pos (by omega) hT
      unfold M5.packingCutoff
      nlinarith [Nat.zero_le (w * T * T)]
    have hrange : ∀ a ∈ M5.Packing.packedSupport r,
        a < M5.packingCutoff w T := by
      intro a ha
      exact lt_trans (M5.Packing.packed_support_range w T r a ha) hcut
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e
            (e + k * T)).card = (M5.Packing.packedSupport r).card := by
          apply M5.RepairSupport.replacement_card <;> assumption
        _ = w := hcard
    · apply M5.RepairSupport.replacement_anchor <;> first | assumption | omega
    · apply M5.RepairSupport.replacement_range <;> assumption
    · unfold M5.PhysicalBridge.remainingGcd at hg
      apply M5.RepairSupport.replacement_connected <;> first | assumption | omega
