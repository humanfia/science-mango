import FrozenTarget_406fe191110b2fa9
theorem M5.BoundedConstruction.repaired_support_properties : QuantumHarnessFrozenTarget := by
  intro w T r s hw hT hr hs e k he hepos hnew hcut hgcd
  have hw0 : 0 < w := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (M5.RepairSupport.replacement_card
      (M5.Packing.packedSupport r) e (e + k * T) he hnew).trans
      (M5.Packing.packed_support_card w T r)
  · exact M5.RepairSupport.replacement_anchor
      (M5.Packing.packedSupport r) e (e + k * T)
      (by omega)
      (M5.Packing.packed_support_anchor w T r hw0 (hr ⟨0, hw0⟩ rfl))
  · apply M5.RepairSupport.replacement_range
      (M5.Packing.packedSupport r) e (e + k * T) (M5.packingCutoff w T)
    · intro a ha
      have harange := M5.Packing.packed_support_range w T r a ha
      simpa using M5.PhysicalBridge.repaired_exponent_cutoff
        w T a 0 0 hT harange (Nat.mul_pos hw0 hT) (by omega)
    · exact hcut
  · apply M5.RepairSupport.replacement_connected
      (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e (e + k * T)
    simpa only [M5.PhysicalBridge.remainingGcd] using hgcd
