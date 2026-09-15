import FrozenTarget_cf24b3e3386b4fd1
theorem M5.BoundedConstruction.packed_repair_hypotheses : QuantumHarnessFrozenTarget := by
  intro w T r s hw hT hr hs hg
  have hw0 : 0 < w := by omega
  have hr0 : 0 ∈ M5.Packing.packedSupport r :=
    M5.Packing.packed_support_anchor w T r hw0 (hr ⟨0, hw0⟩ rfl)
  have hs0 : 0 ∈ M5.Packing.packedSupport s :=
    M5.Packing.packed_support_anchor w T s hw0 (hs ⟨0, hw0⟩ rfl)
  have hrc : 2 ≤ (M5.Packing.packedSupport r).card := by
    rw [M5.Packing.packed_support_card w T r]
    exact hw
  have hsc : 2 ≤ (M5.Packing.packedSupport s).card := by
    rw [M5.Packing.packed_support_card w T s]
    exact hw
  obtain ⟨e, he, hepos⟩ :=
    M5.PhysicalBridge.positive_member (M5.Packing.packedSupport r) hrc hr0
  obtain ⟨hpos, hlt⟩ :=
    M5.PhysicalBridge.remaining_gcd_bounds
      (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e (w * T)
      hsc hs0 (fun b hb => M5.Packing.packed_support_range w T s b hb)
  refine ⟨e, he, hepos, hpos, hlt, ?_⟩
  apply M5.PhysicalBridge.remaining_gcd_feasible T
    (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e he
  rw [M5.PhysicalBridge.packed_combined_gcd w T r s]
  simpa only [M5.BoundedConstruction.tupleSupportGcd] using hg
