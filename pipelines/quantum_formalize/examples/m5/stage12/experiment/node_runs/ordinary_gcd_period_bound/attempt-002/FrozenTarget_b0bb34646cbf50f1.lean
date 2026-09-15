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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree
