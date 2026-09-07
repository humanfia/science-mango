import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Family8Grounding.Family8LongIntervalActiveCoarseNormalizedCardV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8LongIntervalActiveCoarseCardScaleMassBridgeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8LongIntervalActiveCoarseNormalizedCardV2
open Family8LongIntervalActiveCoarseBaseScalarV1
open Family8CanonicalLowerBufferedScaleV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# The parent-mass `X` is the long-interval normalized cardinality

The upstream parent-mass bridge and the downstream long-interval budget use
two names for the same literal quantity `|T_b| b^2`.  This file records the
definitional equality and transports the lower bound without any callback or
additional estimate.
-/

namespace StickyScaleCover

variable {tau b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily tau index}

@[simp]
theorem activeCoarseCardScaleMass_eq_activeCoarseNormalizedCard
    (S : StickyScaleCover fine b) :
    _root_.Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass S =
      activeCoarseNormalizedCard S :=
  rfl

/-- A lower bound produced by the parent-mass bridge feeds the generic
long-interval fine-scale base scalar directly. -/
theorem activeCoarse_halfSq_lower_of_cardScaleMass
    {globalDelta : NNReal} (S : StickyScaleCover fine b)
    {epsilon etaPrime : Real}
    (hglobal : 0 < globalDelta) (htau : 0 < tau)
    (hXLower : globalDelta ^ etaPrime <=
      _root_.Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass S)
    (hratio : b / tau <= globalDelta ^ (-epsilon)) :
    (globalDelta : ENNReal) ^ (etaPrime + 2 * epsilon) / 2 <=
      (S.activeCoarse.card : ENNReal) *
        ((tau : ENNReal) ^ 2 / 2) := by
  apply activeCoarse_halfSq_lower_of_normalizedCard S hglobal htau
  · simpa only [activeCoarseCardScaleMass_eq_activeCoarseNormalizedCard]
      using hXLower
  · exact hratio

/-- Canonical buffered-scale instance; the ratio premise is discharged by
the sharp existing scale theorem. -/
theorem canonicalLowerBufferedScale_activeCoarse_halfSq_lower_of_cardScaleMass
    {globalDelta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily tau index}
    {epsilon etaPrime : Real}
    (S : StickyScaleCover fine
      (canonicalLowerBufferedScale tau theta epsilon))
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (hthetaOne : theta <= 1) (hepsilon : 0 <= epsilon)
    (hXLower : globalDelta ^ etaPrime <=
      _root_.Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass S) :
    (globalDelta : ENNReal) ^ (etaPrime + 2 * epsilon) / 2 <=
      (S.activeCoarse.card : ENNReal) *
        ((tau : ENNReal) ^ 2 / 2) := by
  exact activeCoarse_halfSq_lower_of_cardScaleMass S hglobal
    (hglobal.trans_le hglobalTau)
    hXLower
    (canonicalLowerBufferedScale_div_tau_le_delta_rpow_neg
      hglobal hglobalTau hthetaOne hepsilon)

/-- Direct canonical weighted-budget endpoint.  Once the geometric chain
produces the parent-card `X` lower bound, no separate ratio or definitional
identity premise remains. -/
theorem weightedSelected_baseBudget_of_canonicalCardScaleMassLower
    {globalDelta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum tau index)
    {epsilon etaPrime loss : Real}
    {S : StickyScaleCover D.family
      (canonicalLowerBufferedScale tau theta epsilon)}
    {B A : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (hthetaOne : theta <= 1) (hepsilon : 0 <= epsilon)
    (htauHalf : tau <= (2 : NNReal)⁻¹)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hXLower : globalDelta ^ etaPrime <=
      _root_.Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass S)
    (hscalarCap :
      B * (A * volume (unitBallBody : Set Space)) <=
        (tau : ENNReal) ^ (-loss) *
          ((globalDelta : ENNReal) ^
            (etaPrime + 2 * epsilon) / 2)) :
    A * volume (unitBallBody : Set Space) <=
      (tau : ENNReal) ^ (-loss) *
        (_root_.Family8GeneralizedKatzTaoMultiplicityV1.restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  apply weightedSelected_baseBudget_of_normalizedActiveCoarseLower
    D W hglobal (hglobal.trans_le hglobalTau) htauHalf hB0 hBTop
  · simpa only [activeCoarseCardScaleMass_eq_activeCoarseNormalizedCard]
      using hXLower
  · exact canonicalLowerBufferedScale_div_tau_le_delta_rpow_neg
      hglobal hglobalTau hthetaOne hepsilon
  · exact hscalarCap

#print axioms activeCoarseCardScaleMass_eq_activeCoarseNormalizedCard
#print axioms activeCoarse_halfSq_lower_of_cardScaleMass
#print axioms
  canonicalLowerBufferedScale_activeCoarse_halfSq_lower_of_cardScaleMass
#print axioms
  weightedSelected_baseBudget_of_canonicalCardScaleMassLower

end StickyScaleCover
end
end Family8LongIntervalActiveCoarseCardScaleMassBridgeV2
