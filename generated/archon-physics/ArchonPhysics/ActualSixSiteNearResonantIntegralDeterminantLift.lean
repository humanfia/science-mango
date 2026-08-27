import ArchonPhysics.ActualSixSiteNearResonantIntegralDeterminantScaling

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate

open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink

/-- The transparent integer matrix is exactly `99^15` times the existing
rational residual multiplication matrix. -/
theorem transparentClearedMultiplicationInt_map_rat :
    transparentClearedMultiplicationInt.map (Int.castRingHom Rat) =
      (99 : Rat) ^ 15 • residualMultiplicationRat := by
  classical
  ext i j
  simp only [transparentClearedMultiplicationInt, Matrix.map_apply,
    Matrix.sum_apply, Matrix.smul_apply, map_sum, map_mul, map_pow,
    smul_eq_mul, residualMultiplicationRat,
    cubeMultiplication, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have ht := congrArg (fun M => M i j)
    (tensorMonomial_transparentCompanionInt_map_rat a)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at ht
  have hc := transparentResidualCoeffInt_cast_rat a
  change (Int.castRingHom Rat) (transparentResidualCoeffInt a) = _ at hc
  rw [hc, ht]
  have hcast99 : (Int.castRingHom Rat) (99 : Int) = (99 : Rat) := rfl
  rw [hcast99]
  have hdegree := cubeDegree_le_twelve a
  have hp :
      (99 : Rat) ^ 3 * (99 : Rat) ^ (12 - cubeDegree a) *
          (99 : Rat) ^ cubeDegree a = (99 : Rat) ^ 15 := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    ((99 : Rat) ^ 3 * residualCube a) *
          (99 : Rat) ^ (12 - cubeDegree a) *
          ((99 : Rat) ^ cubeDegree a * tensorMonomial companionRat a i j) =
        ((99 : Rat) ^ 3 * (99 : Rat) ^ (12 - cubeDegree a) *
          (99 : Rat) ^ cubeDegree a) *
            (residualCube a * tensorMonomial companionRat a i j) := by ring
    _ = (99 : Rat) ^ 15 *
          (residualCube a * tensorMonomial companionRat a i j) := by rw [hp]

/-- Modular scalar relating the transparent integer matrix to the checked
residual multiplication operator. -/
def transparentModularScale103 : ZMod 103 :=
  (99 : ZMod 103) ^ 15 * (53 : ZMod 103)⁻¹

theorem inv_fiftyThree_mod_103 :
    (53 : ZMod 103)⁻¹ = 35 := by
  exact ZMod.inv_eq_of_mul_eq_one 103 53 35 (by reduce_mod_char)

theorem transparentModularScale103_ne_zero :
    transparentModularScale103 ≠ 0 := by
  unfold transparentModularScale103
  rw [inv_fiftyThree_mod_103]
  reduce_mod_char
  decide

theorem transparentClearedMultiplicationInt_map_103 :
    transparentClearedMultiplicationInt.map (Int.castRingHom (ZMod 103)) =
      transparentModularScale103 • residualMultiplication103 := by
  classical
  ext i j
  simp only [transparentClearedMultiplicationInt, Matrix.map_apply,
    Matrix.sum_apply, Matrix.smul_apply, map_sum, map_mul, map_pow,
    smul_eq_mul,
    ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink.residualMultiplication103,
    ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink.cubeMultiplication,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have ht := congrArg (fun M => M i j)
    (tensorMonomial_transparentCompanionInt_map_103 a)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at ht
  have hc := transparentResidualCoeffInt_map_103 a
  change (Int.castRingHom (ZMod 103)) (transparentResidualCoeffInt a) = _ at hc
  rw [hc, ht]
  have hcast99 :
      (Int.castRingHom (ZMod 103)) (99 : Int) = (99 : ZMod 103) := rfl
  rw [hcast99]
  have hdegree := cubeDegree_le_twelve a
  have hp :
      (99 : ZMod 103) ^ 3 * (99 : ZMod 103) ^ (12 - cubeDegree a) *
          (99 : ZMod 103) ^ cubeDegree a = (99 : ZMod 103) ^ 15 := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hscale :
      transparentModularScale103 * (53 : ZMod 103) =
        (99 : ZMod 103) ^ 15 := by
    unfold transparentModularScale103
    rw [inv_fiftyThree_mod_103, mul_assoc]
    have hproduct : (35 : ZMod 103) * 53 = 1 := by reduce_mod_char
    rw [hproduct, mul_one]
  calc
    ((99 : ZMod 103) ^ 3 *
          ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCube103 a) *
        (99 : ZMod 103) ^ (12 - cubeDegree a) *
        ((99 : ZMod 103) ^ cubeDegree a *
          tensorMonomial
            ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate.companion103
            a i j) =
      (99 : ZMod 103) ^ 15 *
        (ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCube103 a *
          tensorMonomial
            ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate.companion103
            a i j) := by
      rw [← hp]
      ring
    _ = _ := by
      rw [← hscale]
      ring

end ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate
