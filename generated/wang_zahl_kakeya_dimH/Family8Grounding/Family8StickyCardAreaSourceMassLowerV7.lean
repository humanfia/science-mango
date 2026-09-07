import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

/-!
# Active-parent card-area lower bound for source mass, V2

V1 is a universe-polymorphic draft.  This endpoint-facing clean successor
uses the repository's universe-zero family convention.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyCardAreaSourceMassLowerV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverFrostmanInheritanceV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A lower density bound pays the active-parent-card multiple of one
half-square tube volume in the literal source shading. -/
theorem densityFloor_mul_activeCoarse_half_sq_le_sourceMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {densityFloor : ENNReal}
    (hdensity : densityFloor ≤
      (sourceActiveFineShading (toConvexFactorization S) Y).shadingDensity) :
    densityFloor *
        ((S.activeCoarse.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2)) ≤
      (sourceActiveFineShading
        (toConvexFactorization S) Y).shadingMass := by
  let Z := sourceActiveFineShading (toConvexFactorization S) Y
  have hdeltaSq0 : ((delta : ENNReal) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne')
  have hdeltaSqTop : ((delta : ENNReal) ^ 2) ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcardNat : S.activeCoarse.card ≤ S.activeFine.card :=
    activeCoarse_card_le_activeFine_card S
  have hcard : (S.activeCoarse.card : ENNReal) ≤
      (S.activeFine.card : ENNReal) := by exact_mod_cast hcardNat
  have hfamily :
      (S.activeCoarse.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) ≤
        familyVolume (sourceActiveFineFamily (toConvexFactorization S)) := by
    calc
      (S.activeCoarse.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) ≤
        (S.activeFine.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) := mul_le_mul' hcard le_rfl
      _ = ∑ _i ∈ S.activeFine,
          ((delta : ENNReal) ^ 2 / 2) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
      _ ≤ ∑ i ∈ S.activeFine,
          volume (fine.tubes i).carrier := by
        exact Finset.sum_le_sum fun i _hi =>
          (fine.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
      _ = familyVolume
          (sourceActiveFineFamily (toConvexFactorization S)) := by
        unfold sourceActiveFineFamily
        rw [Submission.Kakeya.ConvexFactoring.HeavyParentSelection.selectedCoarseFamily_volume]
        simp only [toConvexFactorization_fine,
          UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    densityFloor *
        ((S.activeCoarse.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2)) ≤
      Z.shadingDensity *
        familyVolume (sourceActiveFineFamily (toConvexFactorization S)) :=
      mul_le_mul' hdensity hfamily
    _ = Z.shadingMass := by
      exact shadingDensity_mul_familyVolume Z
    _ = (sourceActiveFineShading
        (toConvexFactorization S) Y).shadingMass := by rfl

#print axioms densityFloor_mul_activeCoarse_half_sq_le_sourceMass

end
end Family8StickyCardAreaSourceMassLowerV7
