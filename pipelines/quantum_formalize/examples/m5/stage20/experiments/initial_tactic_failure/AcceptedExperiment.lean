import M5ArithmeticSubset

theorem M5.ArithmeticSubset.coordinates_support_sum : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (U : Finset ℕ), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U)) = M5.SubsetCharacter.vectorSum U (fun s => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ s))) := by
  intro P hP U
  classical
  simp [M5.SupportPolynomial.ofSupport, M5.SubsetCharacter.vectorSum,
    M5.QuotientCharacter.coordinates, map_sum, Finset.sum_apply]
#print axioms M5.ArithmeticSubset.coordinates_support_sum
