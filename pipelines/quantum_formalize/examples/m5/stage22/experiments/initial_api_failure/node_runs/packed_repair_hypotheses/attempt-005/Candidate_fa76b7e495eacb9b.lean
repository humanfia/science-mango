import FrozenTarget_fa76b7e495eacb9b
theorem M5.BoundedConstruction.packed_repair_hypotheses : QuantumHarnessFrozenTarget := by
  intros w T r s hw hT hr hs hg
  have hrc := M5.Packing.packed_support_card w T r
  have hsc := M5.Packing.packed_support_card w T s
  have hrr := M5.Packing.packed_support_range w T r
  have hsr := M5.Packing.packed_support_range w T s
  have hr0 : 0 ∈ M5.Packing.packedSupport r := by
    unfold M5.Packing.packedSupport
    apply Finset.mem_image.mpr
    refine ⟨⟨0, by omega⟩, by simp, ?_⟩
    have hz := hr ⟨0, by omega⟩ rfl
    dsimp at hz ⊢
    simp_all
  have hs0 : 0 ∈ M5.Packing.packedSupport s := by
    unfold M5.Packing.packedSupport
    apply Finset.mem_image.mpr
    refine ⟨⟨0, by omega⟩, by simp, ?_⟩
    have hz := hs ⟨0, by omega⟩ rfl
    dsimp at hz ⊢
    simp_all
  have hrc2 : 2 ≤ (M5.Packing.packedSupport r).card := by omega
  have hsc2 : 2 ≤ (M5.Packing.packedSupport s).card := by omega
  have hp : ∃ e ∈ M5.Packing.packedSupport r, 0 < e := by
    apply M5.PhysicalBridge.positive_member <;> assumption
  obtain ⟨e, he, hep⟩ := hp
  have hb : 0 < M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e ∧
      M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e < w * T := by
    apply M5.PhysicalBridge.remaining_gcd_bounds <;> first | assumption | omega
  refine ⟨e, he, hep, hb.1, hb.2, ?_⟩
  apply M5.PhysicalBridge.remaining_gcd_feasible <;>
    first
    | assumption
    | simpa [hg] using M5.Packing.packed_combined_gcd w T r s
    | simpa [hg] using M5.PhysicalBridge.packed_combined_gcd w T r s
    | solve_by_elim [M5.Packing.packed_combined_gcd]
    | solve_by_elim [M5.PhysicalBridge.packed_combined_gcd]
    | exact?
