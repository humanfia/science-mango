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

theorem M5.ArithmeticSubset.numerator_exact : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.numerator P hP W k z = (2 : ℤ) ^ P.natDegree * (((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ) := by
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

theorem M5.ArithmeticSubset.n_exact : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.n P hP W k z = (((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ) := by
  intro P hP W k z
  classical
  unfold M5.ArithmeticSubset.n
  rw [M5.ArithmeticSubset.numerator_exact P hP W k z]
  have h : (2 : ℤ) ^ P.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [h]

theorem M5.ArithmeticSubset.n_nonnegative : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticSubset.n P hP W k z := by
  intro P hP W k z
  classical
  rw [M5.ArithmeticSubset.n_exact P hP W k z]
  exact Int.natCast_nonneg _
#print axioms M5.ArithmeticSubset.character_sign
#print axioms M5.ArithmeticSubset.binomial_coefficient
#print axioms M5.ArithmeticSubset.coordinates_support_sum
#print axioms M5.ArithmeticSubset.numerator_exact
#print axioms M5.ArithmeticSubset.n_exact
#print axioms M5.ArithmeticSubset.n_nonnegative
