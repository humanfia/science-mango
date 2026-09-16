import FrozenTarget_5d8774fac69ce4c3
theorem M8.Solver.originalF_signature : QuantumHarnessFrozenTarget := by
  intro N inst c
  have ha := Nat.le_of_lt (M7.Supports.degree_lt N c.1)
  have hb := Nat.le_of_lt (M7.Supports.degree_lt N c.2)
  have hm := le_of_eq (M6.Coordinates.modulus_monic_degree N).2
  have h := (M6.Euclid.preprocess_correct_cost N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N) ha hb hm).1
  simpa only [M8.Solver.originalF, M8.PhysicalBridge.signature, M7.RecipeSignature.signature, M6.Cyclic.signature, M6.Euclid.normalized_gcd, gcd_comm] using h
