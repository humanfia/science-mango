import M5AnchoredCount

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z : AdjoinRoot P), M5.QuotientCharacter.value P hP lam z = 1 ∨ M5.QuotientCharacter.value P hP lam z = -1 := @M5.ArithmeticSubset.character_sign
#print axioms M5.ArithmeticSubset.character_sign
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (U : Finset ℕ), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U)) = M5.SubsetCharacter.vectorSum U (fun s => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ s))) := @M5.ArithmeticSubset.coordinates_support_sum
#print axioms M5.ArithmeticSubset.coordinates_support_sum
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (lam : M5.Character.BinaryVector P.natDegree), M5.ArithmeticSubset.binomialTerm P hP W k lam = (M5.SubsetCharacter.signedProduct W (M5.ArithmeticSubset.monomialValue P hP lam)).coeff k := @M5.ArithmeticSubset.binomial_coefficient
#print axioms M5.ArithmeticSubset.binomial_coefficient
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.numerator P hP W k z = (2 : ℤ) ^ P.natDegree * (((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ) := @M5.ArithmeticSubset.numerator_exact
#print axioms M5.ArithmeticSubset.numerator_exact
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.n P hP W k z = (((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ) := @M5.ArithmeticSubset.n_exact
#print axioms M5.ArithmeticSubset.n_exact
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticSubset.n P hP W k z := @M5.ArithmeticSubset.n_nonnegative
#print axioms M5.ArithmeticSubset.n_nonnegative
