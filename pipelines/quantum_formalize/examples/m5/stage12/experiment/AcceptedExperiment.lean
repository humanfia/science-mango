import M5Signature

theorem M5.Signature.binary_monic : ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic := by
  change ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic
  intro P hP
  have h : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  change P.leadingCoeff = 1
  exact h P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP)

theorem M5.Signature.divisor_constant_one : ∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1 := by
  change ∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1
  intro P a hdiv ha
  obtain ⟨q, rfl⟩ := hdiv
  rw [Polynomial.mul_coeff_zero] at ha
  have h : ∀ c d : ZMod 2, c * d = 1 → c = 1 := by decide
  exact h (P.coeff 0) (q.coeff 0) ha

theorem M5.Signature.binary_dvd_antisymm : ∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q := by
  change ∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q
  intro P Q hPQ hQP
  by_cases hP : P = 0
  · subst P
    exact (zero_dvd_iff.mp hPQ).symm
  by_cases hQ : Q = 0
  · subst Q
    exact zero_dvd_iff.mp hQP
  exact Polynomial.eq_of_monic_of_associated
    (M5.Signature.binary_monic P hP)
    (M5.Signature.binary_monic Q hQ)
    (associated_of_dvd_dvd hPQ hQP)

theorem M5.Signature.ordinary_gcd_properties : ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → (EuclideanDomain.gcd a b).Monic ∧ (EuclideanDomain.gcd a b).coeff 0 = 1 ∧ (EuclideanDomain.gcd a b).natDegree ≤ b.natDegree := by
  change ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → (EuclideanDomain.gcd a b).Monic ∧ (EuclideanDomain.gcd a b).coeff 0 = 1 ∧ (EuclideanDomain.gcd a b).natDegree ≤ b.natDegree
  intro a b ha hb
  have hc : (EuclideanDomain.gcd a b).coeff 0 = 1 :=
    M5.Signature.divisor_constant_one _ a (EuclideanDomain.gcd_dvd_left a b) ha
  have hg : EuclideanDomain.gcd a b ≠ 0 := by
    intro h
    simp [h] at hc
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  exact ⟨M5.Signature.binary_monic _ hg, hc,
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right a b) hb0⟩

theorem M5.Signature.exact_signature_lift : ∀ (a b : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → M5.completeSignature a b (T+j*E) = M5.completeSignature a b T := by
  change ∀ (a b : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → M5.completeSignature a b (T+j*E) = M5.completeSignature a b T
  intro a b T E j hE
  unfold M5.completeSignature
  have lift (D : M5.BinaryPolynomial) (hD : D ∣ EuclideanDomain.gcd a b) :
      D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T := by
    first
    | apply M5.Lift.common_divisors_lift <;> assumption
    | symm; apply M5.Lift.common_divisors_lift <;> assumption
  apply M5.Signature.binary_dvd_antisymm
  · apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.gcd_dvd_left _ _
    · exact (lift _ (EuclideanDomain.gcd_dvd_left _ _)).mp (EuclideanDomain.gcd_dvd_right _ _)
  · apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.gcd_dvd_left _ _
    · exact (lift _ (EuclideanDomain.gcd_dvd_left _ _)).mpr (EuclideanDomain.gcd_dvd_right _ _)

theorem M5.Signature.ordinary_gcd_period_bound : ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree := by
  change ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree
  intro a b ha hb
  obtain ⟨hm, hc, hd⟩ := M5.Signature.ordinary_gcd_properties a b ha hb
  have hl := M5.Period.period_law (EuclideanDomain.gcd a b) hm hc
  have hbound := M5.Period.period_cardinality_bound (EuclideanDomain.gcd a b) hm hc
  refine ⟨hl.1, hbound.trans ?_⟩
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hd
#print axioms M5.Signature.binary_monic
#print axioms M5.Signature.binary_dvd_antisymm
#print axioms M5.Signature.divisor_constant_one
#print axioms M5.Signature.exact_signature_lift
#print axioms M5.Signature.ordinary_gcd_properties
#print axioms M5.Signature.ordinary_gcd_period_bound
