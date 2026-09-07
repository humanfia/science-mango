import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import Family8Grounding.Family8StickyDensityAwareCoverLossPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Power envelope for the actual shading-aware Sticky cover loss

The shading-aware selector divides the exact active-parent cover cost by the
actual active shading mass.  The existing card-scale-mass geometry controls
the numerator, while the source Frostman mass floor controls that literal
denominator.  No body-mass replacement is made.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareCoverLossPowerEnvelopeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyParentAggregatedDensityTransportV3.StickyScaleCover
open Family8StickyDensityAwareCoverLossPowerEnvelopeV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Any scalar estimate of the literal numerator gives a bound for the
shading-aware quotient. -/
theorem stickyShadingAwareCoverLoss_le_of_scaled
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A B : ENNReal)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hscaled : A * familyVolume S.activeCoarseFamily ≤
      B * shadingMassOn Y S.activeFine) :
    stickyShadingAwareCoverLoss S Y A ≤ B := by
  unfold stickyShadingAwareCoverLoss
  exact (ENNReal.div_le_iff_le_mul
    (Or.inl hmass)
    (Or.inl (shadingMassOn_ne_top Y S.activeFine))).2 hscaled

/-- The parent tube-volume bound reduces the exact numerator to normalized
active-parent cardinality. -/
theorem stickyShadingAwareCoverLoss_le_of_cardScaleMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A B : ENNReal)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hscaled :
      A * (8 * (activeCoarseCardScaleMass S : ENNReal)) ≤
        B * shadingMassOn Y S.activeFine) :
    stickyShadingAwareCoverLoss S Y A ≤ B := by
  apply stickyShadingAwareCoverLoss_le_of_scaled S Y A B hmass
  calc
    A * familyVolume S.activeCoarseFamily ≤
        A * ((S.activeCoarse.card : ENNReal) *
          (8 * (rho : ENNReal) ^ 2)) :=
      mul_le_mul' le_rfl
        (activeCoarseFamilyVolume_le_card_mul_eight_sq S hrhoHalf)
    _ = A * (8 * ((S.activeCoarse.card : ENNReal) *
          (rho : ENNReal) ^ 2)) := by ac_rfl
    _ = A * (8 * (activeCoarseCardScaleMass S : ENNReal)) := by
      simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
        ENNReal.coe_natCast, ENNReal.coe_pow]
    _ ≤ B * shadingMassOn Y S.activeFine := hscaled

/-- Source coefficient, active-parent card-scale mass, and actual shading
mass power envelopes imply the desired power envelope for the honest
shading-aware loss. -/
theorem stickyShadingAwareCoverLoss_le_rpow_of_powerEnvelopes
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {sourceExponent coefficientExponent xExponent
      absorbExponent coverExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaSmall : delta ≤ densityAwareCoverLossThreshold absorbExponent)
    (hA : A ≤ (delta : ENNReal) ^ (-coefficientExponent))
    (hX : (activeCoarseCardScaleMass S : ENNReal) ≤
      (delta : ENNReal) ^ (-xExponent))
    (hsourceMass : (delta : ENNReal) ^ sourceExponent ≤
      shadingMassOn Y S.activeFine)
    (hexponent : sourceExponent + coefficientExponent + xExponent +
      absorbExponent ≤ coverExponent) :
    stickyShadingAwareCoverLoss S Y A ≤
      (delta : ENNReal) ^ (-coverExponent) := by
  apply stickyShadingAwareCoverLoss_le_of_cardScaleMass
    S Y A ((delta : ENNReal) ^ (-coverExponent)) hmass hrhoHalf
  exact scaledCoverCost_of_powerEnvelopes hdelta hdeltaOne
    habsorbExponent hdeltaSmall hA hX hsourceMass hexponent

#print axioms stickyShadingAwareCoverLoss_le_of_scaled
#print axioms stickyShadingAwareCoverLoss_le_of_cardScaleMass
#print axioms stickyShadingAwareCoverLoss_le_rpow_of_powerEnvelopes

end
end Family8StickyShadingAwareCoverLossPowerEnvelopeV1
