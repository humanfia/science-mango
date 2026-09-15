import M5ArithmeticSubset

noncomputable def M5.Stage20Target.character_sign : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z : AdjoinRoot P), M5.QuotientCharacter.value P hP lam z = 1 ∨ M5.QuotientCharacter.value P hP lam z = -1

#check M5.Stage20Target.character_sign

noncomputable def M5.Stage20Target.coordinates_support_sum : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (U : Finset ℕ), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U)) = M5.SubsetCharacter.vectorSum U (fun s => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ s)))

#check M5.Stage20Target.coordinates_support_sum

noncomputable def M5.Stage20Target.binomial_coefficient : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (lam : M5.Character.BinaryVector P.natDegree), M5.ArithmeticSubset.binomialTerm P hP W k lam = (M5.SubsetCharacter.signedProduct W (M5.ArithmeticSubset.monomialValue P hP lam)).coeff k

#check M5.Stage20Target.binomial_coefficient

noncomputable def M5.Stage20Target.numerator_exact : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.numerator P hP W k z = (2 : ℤ) ^ P.natDegree * (((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ)

#check M5.Stage20Target.numerator_exact

noncomputable def M5.Stage20Target.n_exact : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.n P hP W k z = (((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ)

#check M5.Stage20Target.n_exact

noncomputable def M5.Stage20Target.n_nonnegative : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticSubset.n P hP W k z

#check M5.Stage20Target.n_nonnegative

