import FrozenTarget_de463ca1f3e0bdb7
theorem M5.BoundedConstruction.repaired_support_properties : QuantumHarnessFrozenTarget := by
    intro w T r s hw hT hr hs e k he hepos hnew hbound hg
    classical
    have hinj : Function.Injective (M5.Packing.packedValue r) := by
      intro i j hij
      apply Fin.ext
      have hi := (r i).isLt
      have hj := (r j).isLt
      simp only [M5.Packing.packedValue] at hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hm := Nat.mul_le_mul_right T (Nat.succ_le_of_lt hlt)
        nlinarith
      · have hm := Nat.mul_le_mul_right T (Nat.succ_le_of_lt hgt)
        nlinarith
    have hcard : (M5.Packing.packedSupport r).card = w := by
      unfold M5.Packing.packedSupport
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have hzero : 0 ∈ M5.Packing.packedSupport r := by
      have hz : (r ⟨0, by omega⟩).val = 0 := hr ⟨0, by omega⟩ rfl
      unfold M5.Packing.packedSupport
      apply Finset.mem_image.mpr
      refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
      simpa [M5.Packing.packedValue] using hz
    have hcut : w * T < M5.packingCutoff w T := by
      have hp : 0 < w * T := Nat.mul_pos (by omega) hT
      unfold M5.packingCutoff
      nlinarith
    have hrange : ∀ a ∈ M5.Packing.packedSupport r, a < M5.packingCutoff w T := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      have hi := i.isLt
      have hri := (r i).isLt
      have hm := Nat.mul_le_mul_right T (Nat.succ_le_of_lt hi)
      have hv : M5.Packing.packedValue r i < w * T := by
        unfold M5.Packing.packedValue
        nlinarith
      exact hv.trans hcut
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply M5.RepairSupport.replacement_card <;> assumption
    · apply M5.RepairSupport.replacement_anchor <;> first | assumption | omega
    · apply M5.RepairSupport.replacement_range <;> assumption
    · unfold M5.PhysicalBridge.remainingGcd at hg
      apply M5.RepairSupport.replacement_connected <;> assumption
