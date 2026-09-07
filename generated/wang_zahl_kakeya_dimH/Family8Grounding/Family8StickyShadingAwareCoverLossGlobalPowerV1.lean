import Family8Grounding.Family8StickyShadingAwareCoverLossPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Shading-aware cover loss with a separate global power scale

The cover geometry lives at `fineDelta -> rho`, but its scalar numerator and
source-mass envelopes may be expressed at the original global small scale.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyShadingAwareCoverLossGlobalPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyDensityAwareCoverLossPowerEnvelopeV1
open Family8StickyShadingAwareCoverLossPowerEnvelopeV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {globalDelta delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Global power envelopes for the coefficient, card-scale mass, and actual
source shading control the honest cover loss at an independent fine scale. -/
theorem stickyShadingAwareCoverLoss_le_rpow_of_globalPowerEnvelopes
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {sourceExponent coefficientExponent xExponent
      absorbExponent coverExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hglobalSmall : globalDelta ≤ densityAwareCoverLossThreshold absorbExponent)
    (hA : A ≤ (globalDelta : ENNReal) ^ (-coefficientExponent))
    (hX : (activeCoarseCardScaleMass S : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-xExponent))
    (hsourceMass : (globalDelta : ENNReal) ^ sourceExponent ≤
      shadingMassOn Y S.activeFine)
    (hexponent : sourceExponent + coefficientExponent + xExponent +
      absorbExponent ≤ coverExponent) :
    stickyShadingAwareCoverLoss S Y A ≤
      (globalDelta : ENNReal) ^ (-coverExponent) := by
  apply stickyShadingAwareCoverLoss_le_of_cardScaleMass
    S Y A ((globalDelta : ENNReal) ^ (-coverExponent)) hmass hrhoHalf
  exact scaledCoverCost_of_powerEnvelopes hglobal hglobalOne
    habsorbExponent hglobalSmall hA hX hsourceMass hexponent

#print axioms stickyShadingAwareCoverLoss_le_rpow_of_globalPowerEnvelopes

end
end Family8StickyShadingAwareCoverLossGlobalPowerV1
