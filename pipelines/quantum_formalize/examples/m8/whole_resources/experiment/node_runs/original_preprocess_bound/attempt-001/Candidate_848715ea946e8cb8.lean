import FrozenTarget_848715ea946e8cb8
theorem M8.WholeResources.original_preprocess_bound : QuantumHarnessFrozenTarget := by
  intro N inst c
  have ha := Nat.le_of_lt (M7.Supports.degree_lt N c.1)
  have hb := Nat.le_of_lt (M7.Supports.degree_lt N c.2)
  have hm := le_of_eq (M6.Coordinates.modulus_monic_degree N).2
  exact (M6.Euclid.preprocess_correct_cost N
    (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)
    (M6.Cyclic.modulus N) ha hb hm).2
