import M5BinaryDivisibility
import M5PolynomialExclusion

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

theorem M5.PolynomialExclusion.strict_divisor_extra_factor : ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G := by
  change ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G
  intro F G hFm hFG hG0 hGFne
  have hF0 : F ≠ 0 := hFm.ne_zero
  have hG : G = F * (G / F) :=
    (EuclideanDomain.mul_div_cancel' hF0 hFG).symm
  have hQ0 : G / F ≠ 0 := by
    intro hQ
    apply hG0
    rw [hG, hQ, mul_zero]
  have hQu : ¬ IsUnit (G / F) := by
    rintro ⟨u, hu⟩
    have hGF : G ∣ F := by
      refine ⟨↑(u⁻¹), ?_⟩
      rw [hG, ← hu]
      simp [mul_assoc]
    apply hGFne
    exact M5.Signature.binary_dvd_antisymm G F hGF hFG
  obtain ⟨p, hp, hpQ⟩ := WfDvdMonoid.exists_irreducible_factor hQu hQ0
  exact ⟨p, hp, (M5.PolynomialExclusion.factor_dvd_quotient F G p hF0 hFG).mp hpQ⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b))
