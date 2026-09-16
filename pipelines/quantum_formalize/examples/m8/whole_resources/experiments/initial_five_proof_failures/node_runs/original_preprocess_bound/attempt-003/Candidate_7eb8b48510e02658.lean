import FrozenTarget_7eb8b48510e02658
theorem M8.WholeResources.original_preprocess_bound : QuantumHarnessFrozenTarget := by
  intro N inst c
  change M6.Euclid.preprocessBitCost N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N) ≤ 180 * (N + 1)^3
  have ha : (M7.Supports.polynomial c.1).natDegree < N := by
    apply M7.Supports.degree_lt
  have hb : (M7.Supports.polynomial c.2).natDegree < N := by
    apply M7.Supports.degree_lt
  have ha' := Nat.le_of_lt ha
  have hb' := Nat.le_of_lt hb
  have hm : (M6.Cyclic.modulus N).natDegree ≤ N := by
    unfold M6.Cyclic.modulus
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  aesop (add safe forward M6.Euclid.preprocess_correct_cost)
