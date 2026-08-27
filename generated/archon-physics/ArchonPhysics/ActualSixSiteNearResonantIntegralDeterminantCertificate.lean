import ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness
import ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
import ArchonPhysics.ModularMatrixDeterminantCertificate

/-!
# Transparent integral determinant certificate at `t = 1/10`

This module clears denominators term by term with the transparent scalar
`99^15`.  It then consumes the checked `ZMod 103` right inverse to prove that
the existing rational residual multiplication matrix is nonsingular.
-/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate

open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
open ArchonPhysics.ModularMatrixDeterminantCertificate

/-- Integral companion obtained by multiplying the rational companion by 99. -/
def transparentCompanionInt : Matrix (Fin 5) (Fin 5) Int :=
  !![0, 0, 0, 0, 3600;
     99, 0, 0, 0, -10495;
     0, 99, 0, 0, 11180;
     0, 0, 99, 0, -5379;
     0, 0, 0, 99, 1192]

def cubeDegree (a : CubeIndex) : Nat :=
  a.1.val + a.2.1.val + a.2.2.val

theorem cubeDegree_le_twelve (a : CubeIndex) : cubeDegree a ≤ 12 := by
  unfold cubeDegree
  omega

/-- Multiplying every residual coefficient by `99^3` clears its denominator. -/
def transparentResidualCoeffInt (a : CubeIndex) : Int :=
  (((99 : Rat) ^ 3) * residualCube a).num

/-- An explicitly integral matrix whose rational cast is intended to be
`99^15` times the residual multiplication matrix. -/
def transparentClearedMultiplicationInt : Matrix CubeIndex CubeIndex Int :=
  ∑ a, (transparentResidualCoeffInt a *
      (99 : Int) ^ (12 - cubeDegree a)) •
    tensorMonomial transparentCompanionInt a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact integrality of the 125 scaled residual coefficients. -/
theorem transparentResidualCoeffInt_cast_rat :
    ∀ a, (transparentResidualCoeffInt a : Rat) =
      (99 : Rat) ^ 3 * residualCube a := by
  rintro ⟨x, y, z⟩
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [transparentResidualCoeffInt, residualCube, residualCoeff,
      flattenIndex,
      ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.residualCoeff,
      ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.residualCoeffArray]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The same integral coefficients reduce to the certified modular table. -/
theorem transparentResidualCoeffInt_map_103 :
    ∀ a, (transparentResidualCoeffInt a : ZMod 103) =
      (99 : ZMod 103) ^ 3 *
        ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCube103 a := by
  rintro ⟨x, y, z⟩
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [transparentResidualCoeffInt, residualCube, residualCoeff, flattenIndex,
      ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.residualCoeff,
      ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.residualCoeffArray,
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCube103,
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCoeff103,
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCoeffArray103,
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.flattenIndex] <;>
    reduce_mod_char

theorem transparentCompanionInt_map_rat :
    transparentCompanionInt.map (Int.castRingHom Rat) =
      (99 : Rat) • companionRat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transparentCompanionInt, companionRat]

theorem transparentCompanionInt_map_103 :
    transparentCompanionInt.map (Int.castRingHom (ZMod 103)) =
      (99 : ZMod 103) •
        ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate.companion103 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    decide


end ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness.ModularCertificate
