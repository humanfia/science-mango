import M8Solver

theorem M8.Solver.discovery_span : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Discovery.discover c ≠ none ↔ M8.OrbitSpan.value c ≤ M8.Cutoff.limit N) := by
  intro N inst c w hw hv
  have hleft : c.1.Nonempty := Finset.card_pos.mp (by
    rw [hv.1]
    exact hw)
  have hright : c.2.Nonempty := Finset.card_pos.mp (by
    rw [hv.2.1]
    exact hw)
  exact (M8.Discovery.complete N c).trans
    (M8.OrbitSpan.small_iff N c hleft hright (M8.Cutoff.limit N)).symm

theorem M8.Solver.literal_span_le : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M6.ActualTransfer.span (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ≤ M8.Anchor.span c := by
  intro N inst c w hw hc
  classical
  have degree_bound (s : Finset (ZMod N)) (L : ℕ)
      (hs : ∀ i ∈ s, ZMod.val i ≤ L) :
      (M7.Supports.polynomial s).natDegree ≤ L := by
    by_cases hz : M7.Supports.polynomial s = 0
    · simp [hz]
    · have hm := Polynomial.natDegree_mem_support_of_nonzero hz
      rw [M7.Supports.support] at hm
      rcases Finset.mem_image.mp hm with ⟨i, hi, he⟩
      rw [← he]
      exact hs i hi
  have hb := (M8.Anchor.span_le N c (M8.Anchor.span c)).mp le_rfl
  change max (M7.Supports.polynomial c.1).natDegree
    (M7.Supports.polynomial c.2).natDegree ≤ M8.Anchor.span c
  exact max_le (degree_bound c.1 _ hb.1) (degree_bound c.2 _ hb.2)

theorem M8.Solver.optimizer_present : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.signature c ≠ 1 → ∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) ≠ none := by
  intro N inst c w hw hvalid hsignature choice hdiscover hnone
  have hanchored : M8.PhysicalBridge.Anchored (M7.Action.act (M8.Discovery.action choice) c) :=
    M8.Discovery.anchored N c choice hdiscover
  exact hsignature ((M8.PhysicalBridge.noLogical N c (M8.Discovery.action choice) w hvalid hanchored).mp hnone)
#print axioms M8.Solver.discovery_span
#print axioms M8.Solver.literal_span_le
#print axioms M8.Solver.optimizer_present
