import ArchonPhysics.ActualSixSiteNearResonantModularPolynomialQuotientEvaluation

/-! Evaluation of the certified residual and inverse polynomial tables. -/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
open ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse

noncomputable section

theorem companionEvaluation_residualPolynomial103 :
    companionEvaluation residualPolynomial103 =
      cubeMultiplication companion103 residualCube103 := by
  unfold residualPolynomial103 cubeMultiplication
  simp_rw [map_sum, companionEvaluation_monomial]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [tensorPower, monomialExponent, tensorMonomial]

theorem companionEvaluation_inversePolynomial103 :
    companionEvaluation inversePolynomial103 =
      cubeMultiplication companion103 inverseCube103 := by
  unfold inversePolynomial103 cubeMultiplication
  simp_rw [map_sum, companionEvaluation_monomial]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [tensorPower, monomialExponent, tensorMonomial]

end

end ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation
