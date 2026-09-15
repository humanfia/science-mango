import M5ArithmeticSubset

theorem M5.ArithmeticSubset.character_sign : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z : AdjoinRoot P), M5.QuotientCharacter.value P hP lam z = 1 ∨ M5.QuotientCharacter.value P hP lam z = -1 := by
  intro P hP lam z
  unfold M5.QuotientCharacter.value M5.Character.value M5.Character.bitSign
  simp only [Finset.prod_pow_eq_pow_sum]
  exact neg_one_pow_eq_or ℤ _

theorem M5.ArithmeticSubset.coordinates_support_sum : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (U : Finset ℕ), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U)) = M5.SubsetCharacter.vectorSum U (fun s => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ s))) := by
  intro P hP U
  classical
  simp [M5.SupportPolynomial.ofSupport, M5.SubsetCharacter.vectorSum,
    M5.QuotientCharacter.coordinates, map_sum, Finset.sum_apply]

theorem M5.ArithmeticSubset.binomial_coefficient : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (lam : M5.Character.BinaryVector P.natDegree), M5.ArithmeticSubset.binomialTerm P hP W k lam = (M5.SubsetCharacter.signedProduct W (M5.ArithmeticSubset.monomialValue P hP lam)).coeff k := by
  intro P hP W k lam
  unfold M5.ArithmeticSubset.binomialTerm
  symm
  apply M5.Binomial.signed_coefficient_eval
  all_goals
    intros
    exact M5.ArithmeticSubset.character_sign P hP lam _
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.numerator P hP W k z = (2 : ℤ) ^ P.natDegree * (((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ)
