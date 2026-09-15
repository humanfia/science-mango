import FrozenTarget_5c8115432255280b
theorem M5.BoundedConstruction.packed_repair_hypotheses : QuantumHarnessFrozenTarget := by
  intro w T r s hw hT hr hs hg
  have hrc : (M5.Packing.packedSupport r).card = w := by exact?
  have hsc : (M5.Packing.packedSupport s).card = w := by exact?
  have hrr : ∀ x ∈ M5.Packing.packedSupport r, x < w * T := by
    intro x hx
    exact?
  have hsr : ∀ x ∈ M5.Packing.packedSupport s, x < w * T := by
    intro x hx
    exact?
  have hr0 : 0 ∈ M5.Packing.packedSupport r := by
    unfold M5.BoundedConstruction.anchoredTuple at hr
    first | exact? | aesop
  have hs0 : 0 ∈ M5.Packing.packedSupport s := by
    unfold M5.BoundedConstruction.anchoredTuple at hs
    first | exact? | aesop
  have hrc2 : 2 ≤ (M5.Packing.packedSupport r).card := by omega
  have hsc2 : 2 ≤ (M5.Packing.packedSupport s).card := by omega
  have hp : ∃ e ∈ M5.Packing.packedSupport r, 0 < e := by
    apply M5.PhysicalBridge.positive_member <;> assumption
  obtain ⟨e, he, hep⟩ := hp
  have hb := M5.PhysicalBridge.remaining_gcd_bounds
    (M5.Packing.packedSupport r) (M5.Packing.packedSupport s)
    e (w * T) hsc2 hs0 hsr
  refine ⟨e, he, hep, hb.1, hb.2, ?_⟩
  have hcg := @M5.BoundedConstruction.packed_combined_gcd w T r s
  apply M5.PhysicalBridge.remaining_gcd_feasible <;>
    first
    | assumption
    | simpa only [hcg] using hg
    | aesop
