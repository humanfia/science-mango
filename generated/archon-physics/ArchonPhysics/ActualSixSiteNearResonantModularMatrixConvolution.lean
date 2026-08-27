import ArchonPhysics.ActualSixSiteNearResonantModularMatrixEntry
import ArchonPhysics.ActualSixSiteNearResonantModularDirectConvolution

/-! The checked direct convolution is the origin column of the matrix product. -/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularDirectConvolution

/-- Expansion of the multiplication matrix agrees with the certified direct convolution. -/
theorem residualMultiplication103_mulVec_apply_eq_direct (o : CubeIndex) :
    (residualMultiplication103 *ᵥ inverseOrigin103) o =
      directReducedProductCoeff103 o := by
  classical
  rcases o with ⟨ox, oy, oz⟩
  unfold residualMultiplication103 inverseOrigin103 cubeMultiplication
    directReducedProductCoeff103 sumExponent
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul]
  simp_rw [tensorMonomial_companion103_apply_eq_reduced]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The checked direct convolution is the required inverse origin column. -/
theorem residualMultiplication103_mulVec_inverseOrigin :
    residualMultiplication103 *ᵥ inverseOrigin103 =
      fun i => (1 : Matrix CubeIndex CubeIndex (ZMod 103)) i origin := by
  funext o
  rw [residualMultiplication103_mulVec_apply_eq_direct,
    directReducedProductCoeff103_eq_one]
  by_cases h : o = origin <;> simp [Matrix.one_apply, h]

end ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
