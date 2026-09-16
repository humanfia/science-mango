import FrozenTarget_04a29230bc7b2976
theorem M8.WholeResources.original_preprocess_bound : QuantumHarnessFrozenTarget := by
  intro N inst c
  classical
  change M6.Euclid.preprocessBitCost N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N) ≤ 180 * (N + 1)^3
  have ha := M7.Supports.degree_lt N c.1
  have hb := M7.Supports.degree_lt N c.2
  have ha' : (M7.Supports.polynomial c.1).natDegree ≤ N := by
    first
    | omega
    | exact Polynomial.natDegree_le_of_degree_le (le_of_lt ha)
  have hb' : (M7.Supports.polynomial c.2).natDegree ≤ N := by
    first
    | omega
    | exact Polynomial.natDegree_le_of_degree_le (le_of_lt hb)
  have hm : (M6.Cyclic.modulus N).natDegree ≤ N := by
    unfold M6.Cyclic.modulus
    simpa only [Polynomial.map_one] using
      (Polynomial.natDegree_X_pow_sub_C (R := ZMod 2) (n := N) (r := 1)).le
  have h := M6.Euclid.preprocess_correct_cost N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N)
  aesop
