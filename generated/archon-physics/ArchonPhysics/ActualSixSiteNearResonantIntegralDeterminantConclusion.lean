import ArchonPhysics.ActualSixSiteNearResonantIntegralDeterminantLift
import ArchonPhysics.ActualSixSiteNearResonantModularPolynomialRightInverse

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate

open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
open ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation
open ArchonPhysics.ModularMatrixDeterminantCertificate

/-- The modular inverse, scaled by the explicit inverse `98` of the clearing
scalar `41` modulo 103. -/
def transparentCertifiedRightInverse103 :
    Matrix CubeIndex CubeIndex (ZMod 103) :=
  (98 : ZMod 103) •
    ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink.cubeMultiplication
      ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate.companion103
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.inverseCube103

theorem transparentModularScale103_mul_ninetyEight :
    transparentModularScale103 * (98 : ZMod 103) = 1 := by
  unfold transparentModularScale103
  rw [inv_fiftyThree_mod_103]
  reduce_mod_char

theorem transparentClearedMultiplicationInt_modular_rightInverse :
    transparentClearedMultiplicationInt.map (Int.castRingHom (ZMod 103)) *
        transparentCertifiedRightInverse103 = 1 := by
  rw [transparentClearedMultiplicationInt_map_103]
  unfold transparentCertifiedRightInverse103
  rw [Matrix.smul_mul, Matrix.mul_smul,
    residualMultiplication103_mul_polynomialInverse]
  rw [smul_smul, transparentModularScale103_mul_ninetyEight, one_smul]

local instance fact_one_lt_103 : Fact (1 < (103 : Nat)) := ⟨by norm_num⟩

/-- Nonsingularity of the existing rational residual multiplication matrix.
This is the determinant fact consumed by the fixed-energy specialization. -/
theorem residualMultiplicationRat_det_ne_zero :
    residualMultiplicationRat.det ≠ 0 := by
  exact rat_det_ne_zero_of_modular_right_inverse (p := 103)
    residualMultiplicationRat transparentClearedMultiplicationInt
    transparentCertifiedRightInverse103 ((99 : Rat) ^ 15)
    (by norm_num)
    transparentClearedMultiplicationInt_map_rat
    transparentClearedMultiplicationInt_modular_rightInverse

end ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate
