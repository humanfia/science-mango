import M5PolynomialIndicator

import M5PolynomialExclusionAccepted

example : ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0 := M5.PolynomialExclusion.cyclic_quotient_nonzero

#print axioms M5.PolynomialExclusion.cyclic_quotient_nonzero

example : ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P) := M5.PolynomialExclusion.factor_dvd_quotient

#print axioms M5.PolynomialExclusion.factor_dvd_quotient

example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N := M5.PolynomialExclusion.signature_contains

#print axioms M5.PolynomialExclusion.signature_contains

example : ∀ F G : M5.BinaryPolynomial, F.Monic → F ∣ G → G ≠ 0 → G ≠ F → ∃ p : M5.BinaryPolynomial, Irreducible p ∧ F * p ∣ G := M5.PolynomialExclusion.strict_divisor_extra_factor

#print axioms M5.PolynomialExclusion.strict_divisor_extra_factor

example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p : M5.BinaryPolynomial, Irreducible p → p ∣ M5.cyclicModulus N / F → ¬ (F * p ∣ a ∧ F * p ∣ b)) := M5.PolynomialExclusion.exact_signature_criterion

#print axioms M5.PolynomialExclusion.exact_signature_criterion

example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → (M5.completeSignature a b N = F ↔ ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, ¬ (F * p ∣ a ∧ F * p ∣ b)) := M5.PolynomialExclusion.finite_factor_criterion

#print axioms M5.PolynomialExclusion.finite_factor_criterion
