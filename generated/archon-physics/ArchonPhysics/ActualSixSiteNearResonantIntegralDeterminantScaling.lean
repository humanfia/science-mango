import ArchonPhysics.ActualSixSiteNearResonantIntegralDeterminantCertificate

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate

open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink

theorem transparentCompanionInt_pow_map_rat (n : Nat) :
    (transparentCompanionInt ^ n).map (Int.castRingHom Rat) =
      (99 : Rat) ^ n • companionRat ^ n := by
  rw [Matrix.map_pow, transparentCompanionInt_map_rat, smul_pow]

theorem transparentCompanionInt_pow_map_103 (n : Nat) :
    (transparentCompanionInt ^ n).map (Int.castRingHom (ZMod 103)) =
      (99 : ZMod 103) ^ n •
        ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate.companion103 ^ n := by
  rw [Matrix.map_pow, transparentCompanionInt_map_103, smul_pow]

theorem tensorMonomial_transparentCompanionInt_map_rat (a : CubeIndex) :
    (tensorMonomial transparentCompanionInt a).map (Int.castRingHom Rat) =
      (99 : Rat) ^ cubeDegree a • tensorMonomial companionRat a := by
  ext i j
  rcases i with ⟨ix, iy, iz⟩
  rcases j with ⟨jx, jy, jz⟩
  have hx := congrArg (fun M => M ix jx)
    (transparentCompanionInt_pow_map_rat a.1.val)
  have hy := congrArg (fun M => M iy jy)
    (transparentCompanionInt_pow_map_rat a.2.1.val)
  have hz := congrArg (fun M => M iz jz)
    (transparentCompanionInt_pow_map_rat a.2.2.val)
  simp only [Matrix.map_apply, Matrix.smul_apply] at hx hy hz
  simp only [tensorMonomial, Matrix.map_apply, Matrix.kronecker_apply,
    Matrix.smul_apply, map_mul]
  rw [hx, hy, hz]
  simp only [cubeDegree, pow_add]
  ring

theorem tensorMonomial_transparentCompanionInt_map_103 (a : CubeIndex) :
    (tensorMonomial transparentCompanionInt a).map
        (Int.castRingHom (ZMod 103)) =
      (99 : ZMod 103) ^ cubeDegree a •
        tensorMonomial
          ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate.companion103 a := by
  ext i j
  rcases i with ⟨ix, iy, iz⟩
  rcases j with ⟨jx, jy, jz⟩
  have hx := congrArg (fun M => M ix jx)
    (transparentCompanionInt_pow_map_103 a.1.val)
  have hy := congrArg (fun M => M iy jy)
    (transparentCompanionInt_pow_map_103 a.2.1.val)
  have hz := congrArg (fun M => M iz jz)
    (transparentCompanionInt_pow_map_103 a.2.2.val)
  simp only [Matrix.map_apply, Matrix.smul_apply] at hx hy hz
  simp only [tensorMonomial, Matrix.map_apply, Matrix.kronecker_apply,
    Matrix.smul_apply, map_mul]
  rw [hx, hy, hz]
  simp only [cubeDegree, pow_add]
  ring

end ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate
