import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8
import Family8Grounding.Family8LongIntervalActiveCoarseCardScaleMassBridgeV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalFrostmanWeightedFirstLongBaseBudgetV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ParameterLadderV1
open Family8CanonicalLowerBufferedScaleV4
open Family8StickyParentHullVolumeBoundV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Canonical coarse Frostman constant to the weighted first-long base budget

This is the mechanical composition of the canonical `C_F(T_b)` consumer,
the sharp factor-eight absorption, and the actual weighted selected-volume
bridge.  It accepts neither an abstract `X` nor an `IsFrostmanIn`
certificate.  Its remaining geometric premise `hC` is the literal scalar
canonical-Frostman bound that must be produced by the Family 6 flat-prism
branch; `hscalarCap` is the explicit conflict-loss parameter comparison.
-/

namespace StickyScaleCover

/-- The first-long selected-family base estimate from the literal canonical
active-coarse Frostman scalar bound. -/
theorem weightedSelected_baseBudget_of_parameterLadder_canonicalFrostman
    {globalDelta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum tau index) (hD : D.IsAdmissible)
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta)
    {S : StickyScaleCover D.family
      (canonicalLowerBufferedScale tau theta P.epsilon)}
    {B A : ENNReal} {loss : Real}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta ≤ tau)
    (hthetaOne : theta ≤ 1)
    (hrho : 0 < canonicalLowerBufferedScale tau theta P.epsilon)
    (hrhoHalf : canonicalLowerBufferedScale tau theta P.epsilon ≤
      (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hC : canonicalFrostmanConstant
        S.activeCoarseFamily closedBallFourBody ≤
      (globalDelta : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
    (hdelta : globalDelta ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hscalarCap :
      B * (A * volume (unitBallBody : Set Space)) ≤
        (tau : ENNReal) ^ (-loss) *
          ((globalDelta : ENNReal) ^
            (10 * P.eta j / (P.epsilon * beta) + 2 * P.epsilon) / 2)) :
    A * volume (unitBallBody : Set Space) ≤
      (tau : ENNReal) ^ (-loss) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  have hXLower :
      globalDelta ^ (10 * P.eta j / (P.epsilon * beta)) ≤
        _root_.Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass S :=
    Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8.StickyScaleCover.parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_canonical
      D hD S P j hbeta hglobal hrho hrhoHalf hcoarse hC hdelta
  exact
    Family8LongIntervalActiveCoarseCardScaleMassBridgeV2.StickyScaleCover.weightedSelected_baseBudget_of_canonicalCardScaleMassLower
      D W hglobal hglobalTau hthetaOne P.epsilon_pos.le
        hD.delta_le_half hB0 hBTop hXLower hscalarCap

#print axioms
  weightedSelected_baseBudget_of_parameterLadder_canonicalFrostman

end StickyScaleCover
end
end Family8CanonicalFrostmanWeightedFirstLongBaseBudgetV4
