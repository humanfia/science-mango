import FrozenTarget_686196f28ddc6476
theorem M8.Solver.literal_span_le : QuantumHarnessFrozenTarget := by
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
