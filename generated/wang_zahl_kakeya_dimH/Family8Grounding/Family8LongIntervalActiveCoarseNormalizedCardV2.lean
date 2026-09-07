import Family8Grounding.Family8DoubledParentConflictWeightedLongIntervalBaseBudgetV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8LongIntervalActiveCoarseNormalizedCardV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8DoubledParentConflictWeightedLongIntervalBaseBudgetV2.ScaleCover
open Family8LongIntervalActiveCoarseBaseScalarV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# The concrete long-interval normalized active-parent cardinality

This definition makes the paper quantity `X = b^2 |T_b|` literal for an
actual sticky scale cover.  The definitional identity then disappears from
downstream hypotheses; only the genuine lower bound on `X` remains.
-/

def activeCoarseNormalizedCard
    {tau b : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily tau index}
    (S : StickyScaleCover fine b) : NNReal :=
  (S.activeCoarse.card : NNReal) * b ^ 2

@[simp]
theorem activeCoarseNormalizedCard_eq
    {tau b : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily tau index}
    (S : StickyScaleCover fine b) :
    activeCoarseNormalizedCard S =
      (S.activeCoarse.card : NNReal) * b ^ 2 :=
  rfl

theorem activeCoarse_halfSq_lower_of_normalizedCard
    {globalDelta tau b : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily tau index}
    (S : StickyScaleCover fine b) {epsilon etaPrime : Real}
    (hglobal : 0 < globalDelta) (htau : 0 < tau)
    (hXLower : globalDelta ^ etaPrime <= activeCoarseNormalizedCard S)
    (hratio : b / tau <= globalDelta ^ (-epsilon)) :
    (globalDelta : ENNReal) ^ (etaPrime + 2 * epsilon) / 2 <=
      (S.activeCoarse.card : ENNReal) *
        ((tau : ENNReal) ^ 2 / 2) := by
  exact longInterval_activeCoarse_halfSq_lower
    hglobal htau rfl hXLower hratio

theorem weightedSelected_baseBudget_of_normalizedActiveCoarseLower
    {globalDelta tau b : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum tau index)
    {S : StickyScaleCover D.family b} {B A : ENNReal}
    {epsilon etaPrime loss : Real}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hglobal : 0 < globalDelta) (htau : 0 < tau)
    (htauHalf : tau <= (2 : NNReal)⁻¹)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hXLower : globalDelta ^ etaPrime <= activeCoarseNormalizedCard S)
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
  exact weightedSelected_baseBudget_of_longIntervalX
    D W hglobal htau htauHalf hB0 hBTop rfl hXLower hratio hscalarCap

#print axioms activeCoarseNormalizedCard_eq
#print axioms activeCoarse_halfSq_lower_of_normalizedCard
#print axioms weightedSelected_baseBudget_of_normalizedActiveCoarseLower

end
end Family8LongIntervalActiveCoarseNormalizedCardV2
