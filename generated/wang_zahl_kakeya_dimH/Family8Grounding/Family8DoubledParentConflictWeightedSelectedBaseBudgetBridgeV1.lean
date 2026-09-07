import Family8Grounding.Family8DoubledParentConflictWeightedSelectedVolumeLowerV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedSelectedBaseBudgetBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8DoubledParentConflictWeightedSelectedVolumeLowerV3.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Active-parent scalar budget to the selected Frostman base estimate

The selected-volume bridge retains `activeCoarse.card * delta^2 / 2` with
the same graph loss `B`.  This module packages the exact division-free
scalar premise which is therefore sufficient for the ambient unit-ball
base estimate.  No geometric or cardinal lower bound is hidden here: the
displayed active-parent inequality is precisely the remaining numerical
input.
-/

namespace ScaleCover

/-- A division-free active-parent scalar lower bound closes the literal
selected-family base normalization after cancelling the finite nonzero
conflict loss. -/
theorem weightedSelected_baseBudget_of_activeCoarse_card
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B A : ENNReal} {eta : Real}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hactiveBase :
      B * (A * volume (unitBallBody : Set Space)) ≤
        (delta : ENNReal) ^ (-eta) *
          ((S.activeCoarse.card : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2))) :
    A * volume (unitBallBody : Set Space) ≤
      (delta : ENNReal) ^ (-eta) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  apply (ENNReal.mul_le_mul_iff_right hB0 hBTop).mp
  calc
    B * (A * volume (unitBallBody : Set Space)) ≤
        (delta : ENNReal) ^ (-eta) *
          ((S.activeCoarse.card : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)) := hactiveBase
    _ ≤ (delta : ENNReal) ^ (-eta) *
        (B * (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume) :=
      mul_le_mul' le_rfl
        (activeCoarse_card_mul_half_sq_le_budget_mul_weightedSelected_actualFamilyVolume
          D W hdeltaHalf)
    _ = B * ((delta : ENNReal) ^ (-eta) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume) := by
      ac_rfl

#print axioms weightedSelected_baseBudget_of_activeCoarse_card

end ScaleCover
end
end Family8DoubledParentConflictWeightedSelectedBaseBudgetBridgeV1
