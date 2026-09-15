import FrozenTarget_f82d27af90c8b593
theorem M5.ArithmeticSubset.numerator_exact : QuantumHarnessFrozenTarget := by
  intro P hP W k z
  classical
  trans (2 : ℤ) ^ P.natDegree * (((W.powersetCard k).filter (fun U => M5.SubsetCharacter.vectorSum U (fun s => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ s))) = M5.QuotientCharacter.coordinates P hP z)).card : ℤ)
  · unfold M5.ArithmeticSubset.numerator
    simp only [M5.ArithmeticSubset.binomial_coefficient]
    unfold M5.ArithmeticSubset.monomialValue M5.QuotientCharacter.value
    first
    | apply M5.SubsetCharacter.subset_character_count
    | apply M5.SubsetCount.subset_character_count
    | apply M5.subset_character_count
  · congr 1
    congr 1
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro U hU
    rw [← M5.ArithmeticSubset.coordinates_support_sum P hP U]
    exact (M5.QuotientCharacter.coordinates P hP).injective.eq_iff
