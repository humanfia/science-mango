import M5BinaryDivisibility
import M5PolynomialExclusion

theorem M5.PolynomialExclusion.cyclic_quotient_nonzero : ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0 := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0
  intro F N hN hmonic hdvd hquot
  have hmul := EuclideanDomain.mul_div_cancel' hmonic.ne_zero hdvd
  have hzero : M5.cyclicModulus N = 0 := by
    rw [hquot, mul_zero] at hmul
    exact hmul.symm
  have hcoeff := congrArg (fun p : M5.BinaryPolynomial => p.coeff N) hzero
  simp [M5.cyclicModulus, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_one, Nat.ne_of_gt hN] at hcoeff

theorem M5.PolynomialExclusion.factor_dvd_quotient : ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P) := by
  change ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P)
  intro F P p hF hFP
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      P = F * (P / F) := (EuclideanDomain.mul_div_cancel' hF hFP).symm
      _ = F * (p * q) := congrArg (fun x => F * x) hq
      _ = (F * p) * q := (mul_assoc F p q).symm
  · intro h
    exact EuclideanDomain.dvd_div_of_mul_dvd h

theorem M5.PolynomialExclusion.signature_contains : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N
  intro a b F N ha hb hN
  unfold M5.completeSignature
  repeat' first | assumption | apply EuclideanDomain.dvd_gcd
#print axioms M5.PolynomialExclusion.cyclic_quotient_nonzero
#print axioms M5.PolynomialExclusion.factor_dvd_quotient
#print axioms M5.PolynomialExclusion.signature_contains
