import FrozenTarget_2316b014c1ea8f3e
theorem M5.BoundedConstruction.packed_repair_hypotheses : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro w T r s hw hT hr hs hg
  have hrc : (M5.Packing.packedSupport r).card = w :=
    M5.Packing.packed_support_card w T r
  have hsc : (M5.Packing.packedSupport s).card = w :=
    M5.Packing.packed_support_card w T s
  have hrr : ∀ x ∈ M5.Packing.packedSupport r, x < w * T :=
    M5.Packing.packed_support_range w T r
  have hsr : ∀ x ∈ M5.Packing.packedSupport s, x < w * T :=
    M5.Packing.packed_support_range w T s
  have hr0 : 0 ∈ M5.Packing.packedSupport r := by
    unfold M5.BoundedConstruction.anchoredTuple at hr
    unfold M5.Packing.packedSupport
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp_all
  have hs0 : 0 ∈ M5.Packing.packedSupport s := by
    unfold M5.BoundedConstruction.anchoredTuple at hs
    unfold M5.Packing.packedSupport
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp_all
  have hp : ∃ e ∈ M5.Packing.packedSupport r, 0 < e := by
    apply_rules [M5.PhysicalBridge.positive_member]
    all_goals omega
  obtain ⟨e, he, hep⟩ := hp
  refine ⟨e, he, hep, ?_, ?_, ?_⟩
  · have hb := M5.PhysicalBridge.remaining_gcd_bounds
    aesop
  · have hb := M5.PhysicalBridge.remaining_gcd_bounds
    aesop
  · apply_rules [M5.PhysicalBridge.remaining_gcd_feasible]
    all_goals first | assumption | exact?
