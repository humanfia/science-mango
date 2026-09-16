import FrozenTarget_42fbc510bbc2274c
theorem M8.RawParameters.encoded_dimension : QuantumHarnessFrozenTarget := by
  intro N w inst c hw hc
  have ha : (M7.Supports.polynomial c.1).degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast M7.Supports.degree_lt N c.1
  have hb : (M7.Supports.polynomial c.2).degree < (N : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast M7.Supports.degree_lt N c.2
  simpa only [M6.Final.encodedQubits, M6.ActualCounts.f,
    M8.PhysicalBridge.signature, M7.RecipeSignature.signature,
    M7.Domain.signature] using
    (M6.ActualCounts.encoded_dimension N
      (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ha hb)
