import FrozenTarget_64ddb8db0affd116
theorem M5.BoundedConstruction.repaired_support_properties : QuantumHarnessFrozenTarget := by
  intro w T r s hw hT hr hs e k he hepos hnew hbound hg
  have hcard : (M5.Packing.packedSupport r).card = w := by
    exact?
  have hzero : 0 ∈ M5.Packing.packedSupport r := by
    first
    | exact?
    | unfold M5.BoundedConstruction.anchoredTuple at hr
      exact?
  have hcut : w * T < M5.packingCutoff w T := by
    first
    | exact?
    | unfold M5.packingCutoff
      nlinarith
  have hrange : ∀ a ∈ M5.Packing.packedSupport r, a < M5.packingCutoff w T := by
    intro a ha
    have ha' : a < w * T := by
      exact?
    exact lt_trans ha' hcut
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)).card =
          (M5.Packing.packedSupport r).card :=
        M5.RepairSupport.replacement_card _ _ _ he hnew
      _ = w := hcard
  · apply M5.RepairSupport.replacement_anchor <;> first | assumption | omega
  · apply M5.RepairSupport.replacement_range <;> assumption
  · unfold M5.PhysicalBridge.remainingGcd at hg
    apply M5.RepairSupport.replacement_connected <;> assumption
