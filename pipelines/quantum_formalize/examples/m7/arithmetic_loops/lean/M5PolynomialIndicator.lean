import M5Checkpoint90
import M5PolynomialExclusion

open scoped BigOperators
namespace M5.PolynomialIndicator
noncomputable def factorExclusionSum (a b F : M5.BinaryPolynomial) (N : ℕ) : ℤ := by
  classical
  exact ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
    (-1 : ℤ)^S.card * (if F * (∏ p ∈ S, p) ∣ a ∧ F * (∏ p ∈ S, p) ∣ b then 1 else 0)
end M5.PolynomialIndicator
