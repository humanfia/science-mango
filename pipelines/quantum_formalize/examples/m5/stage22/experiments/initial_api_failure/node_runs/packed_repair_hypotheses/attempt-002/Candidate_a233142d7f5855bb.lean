import FrozenTarget_a233142d7f5855bb
theorem M5.BoundedConstruction.packed_repair_hypotheses : QuantumHarnessFrozenTarget := by
  intro w T r s hw hT hr hs hg
  have hcr : (M5.Packing.packedSupport r).card = w := by exact?
  have hcs : (M5.Packing.packedSupport s).card = w := by exact?
  have hrr : ∀ x ∈ M5.Packing.packedSupport r, x < w * T := by exact?
  have hsr : ∀ x ∈ M5.Packing.packedSupport s, x < w * T := by exact?
  have hzr : 0 ∈ M5.Packing.packedSupport r := by
    unfold M5.BoundedConstruction.anchoredTuple at hr
    exact?
  have hzs : 0 ∈ M5.Packing.packedSupport s := by
    unfold M5.BoundedConstruction.anchoredTuple at hs
    exact?
  have hcr' : 2 ≤ (M5.Packing.packedSupport r).card := by omega
  have hcs' : 2 ≤ (M5.Packing.packedSupport s).card := by omega
  obtain ⟨e, he, hepos⟩ : ∃ e ∈ M5.Packing.packedSupport r, 0 < e := by
    apply_rules [M5.PhysicalBridge.positive_member]
  have hb : 0 < M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e ∧
      M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e < w * T := by
    apply_rules [M5.PhysicalBridge.remaining_gcd_bounds]
  refine ⟨e, he, hepos, hb.1, hb.2, ?_⟩
  apply_rules [M5.PhysicalBridge.remaining_gcd_feasible,
    M5.BoundedConstruction.packed_combined_gcd]
