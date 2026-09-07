import Family8Grounding.Family8DoubledParentConflictWeightedSelectedBaseBudgetBridgeV1
import Family8Grounding.Family8LongIntervalActiveCoarseBaseScalarV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedLongIntervalBaseBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8DoubledParentConflictWeightedSelectedBaseBudgetBridgeV1.ScaleCover
open Family8LongIntervalActiveCoarseBaseScalarV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Long-interval scalar input for the weighted selected-family base budget

This connector exposes the two genuinely missing inputs: the identity
`X = b^2 * |activeCoarse|` and one final pure scalar comparison.  Everything
between those inputs and the literal selected-family base estimate is
mechanical.  No self-improvement conclusion is stored in a structure field.
-/

namespace ScaleCover

theorem weightedSelected_baseBudget_of_longIntervalX
    {globalDelta tau b X : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum tau index)
    {S : StickyScaleCover D.family b} {B A : ENNReal}
    {epsilon etaPrime loss : Real}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hglobal : 0 < globalDelta) (htau : 0 < tau)
    (htauHalf : tau <= (2 : NNReal)⁻¹)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hX : X = (S.activeCoarse.card : NNReal) * b ^ 2)
    (hXLower : globalDelta ^ etaPrime <= X)
    (hratio : b / tau <= globalDelta ^ (-epsilon))
    (hscalarCap :
      B * (A * volume (unitBallBody : Set Space)) <=
        (tau : ENNReal) ^ (-loss) *
          ((globalDelta : ENNReal) ^
            (etaPrime + 2 * epsilon) / 2)) :
    A * volume (unitBallBody : Set Space) <=
      (tau : ENNReal) ^ (-loss) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  have hactiveLower :
      (globalDelta : ENNReal) ^ (etaPrime + 2 * epsilon) / 2 <=
        (S.activeCoarse.card : ENNReal) *
          ((tau : ENNReal) ^ 2 / 2) :=
    longInterval_activeCoarse_halfSq_lower
      hglobal htau hX hXLower hratio
  apply weightedSelected_baseBudget_of_activeCoarse_card
    D W htauHalf hB0 hBTop
  calc
    B * (A * volume (unitBallBody : Set Space)) <=
        (tau : ENNReal) ^ (-loss) *
          ((globalDelta : ENNReal) ^
            (etaPrime + 2 * epsilon) / 2) := hscalarCap
    _ <= (tau : ENNReal) ^ (-loss) *
          ((S.activeCoarse.card : ENNReal) *
            ((tau : ENNReal) ^ 2 / 2)) :=
      mul_le_mul' le_rfl hactiveLower

#print axioms weightedSelected_baseBudget_of_longIntervalX

end ScaleCover
end
end Family8DoubledParentConflictWeightedLongIntervalBaseBudgetV2
