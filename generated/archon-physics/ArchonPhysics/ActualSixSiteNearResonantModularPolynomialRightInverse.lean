import ArchonPhysics.ActualSixSiteNearResonantModularPolynomialTermEvaluation

/-! The kernel-clean modular matrix right inverse obtained by polynomial evaluation. -/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
open ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse

noncomputable section

/-- The polynomial Bezout identity evaluated in the tensor companion
representation gives a full modular right inverse without any finite native
decision. -/
theorem residualMultiplication103_mul_polynomialInverse :
    residualMultiplication103 *
        cubeMultiplication companion103 inverseCube103 = 1 := by
  have h := congrArg companionEvaluation residual_inverse_polynomial_identity
  simp only [map_mul, map_add, map_one, companionEvaluation_C,
    companionEvaluation_residualPolynomial103,
    companionEvaluation_inversePolynomial103,
    companionEvaluation_quotientQuintic103, zero_mul, add_zero] at h
  simpa [residualMultiplication103, Matrix.smul_mul] using h

end

end ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation
