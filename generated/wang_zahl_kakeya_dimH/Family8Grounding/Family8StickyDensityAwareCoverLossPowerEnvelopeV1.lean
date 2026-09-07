import Family8Grounding.Family8StickyDensityAwareLogBranchingCoverLossV4
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power envelope for the density-aware Sticky cover loss

The exact loss is controlled by the source Katz--Tao coefficient times the
normalized active-parent cardinality, divided by retained source mass.  This
module performs precisely that scalar cancellation and absorbs only the
fixed tube-volume constant eight.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareCoverLossPowerEnvelopeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyDensityAwareLogBranchingCoverLossV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Uniform threshold which absorbs the sole fixed factor eight. -/
def densityAwareCoverLossThreshold (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 8 absorbExponent

theorem densityAwareCoverLossThreshold_pos (absorbExponent : Real) :
    0 < densityAwareCoverLossThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- Pure scalar form of the density-aware cover-cost estimate. -/
theorem scaledCoverCost_of_powerEnvelopes
    {d : NNReal} {A X sourceMass : ENNReal}
    {sourceExponent coefficientExponent xExponent
      absorbExponent coverExponent : Real}
    (hd : 0 < d) (hdOne : d ≤ 1)
    (habsorbExponent : 0 < absorbExponent)
    (hdSmall : d ≤ densityAwareCoverLossThreshold absorbExponent)
    (hA : A ≤ (d : ENNReal) ^ (-coefficientExponent))
    (hX : X ≤ (d : ENNReal) ^ (-xExponent))
    (hsourceMass : (d : ENNReal) ^ sourceExponent ≤ sourceMass)
    (hexponent :
      sourceExponent + coefficientExponent + xExponent +
        absorbExponent ≤ coverExponent) :
    A * (8 * X) ≤
      (d : ENNReal) ^ (-coverExponent) * sourceMass := by
  have hd0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : (d : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (d : ENNReal) ≤ 1 := by exact_mod_cast hdOne
  have hfixed : (8 : ENNReal) ≤
      (d : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExponent hd hdSmall
  calc
    A * (8 * X) = 8 * A * X := by ac_rfl
    _ ≤ (d : ENNReal) ^ (-absorbExponent) *
          (d : ENNReal) ^ (-coefficientExponent) *
          (d : ENNReal) ^ (-xExponent) :=
      mul_le_mul' (mul_le_mul' hfixed hA) hX
    _ = (d : ENNReal) ^
          (-(absorbExponent + coefficientExponent + xExponent)) := by
      rw [show -(absorbExponent + coefficientExponent + xExponent) =
          (-absorbExponent + -coefficientExponent) + -xExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ ≤ (d : ENNReal) ^ (sourceExponent - coverExponent) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN
      linarith
    _ = (d : ENNReal) ^ (-coverExponent) *
          (d : ENNReal) ^ sourceExponent := by
      rw [show sourceExponent - coverExponent =
          -coverExponent + sourceExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ ≤ (d : ENNReal) ^ (-coverExponent) * sourceMass :=
      mul_le_mul' le_rfl hsourceMass

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The generic power envelopes for the source coefficient, normalized
parent cardinality, and active-fine mass imply the desired power envelope
for the honest density-aware loss. -/
theorem stickyDensityAwareCoverLoss_le_rpow_of_powerEnvelopes
    (S : StickyScaleCover fine rho) (A : ENNReal)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hactive : S.activeFine.Nonempty)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {sourceExponent coefficientExponent xExponent
      absorbExponent coverExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaSmall :
      delta ≤ densityAwareCoverLossThreshold absorbExponent)
    (hA : A ≤ (delta : ENNReal) ^ (-coefficientExponent))
    (hX : (activeCoarseCardScaleMass S : ENNReal) ≤
      (delta : ENNReal) ^ (-xExponent))
    (hsourceMass : (delta : ENNReal) ^ sourceExponent ≤
      bodyMassOn fine.bodyFamily S.activeFine)
    (hexponent :
      sourceExponent + coefficientExponent + xExponent +
        absorbExponent ≤ coverExponent) :
    stickyDensityAwareCoverLoss S A ≤
      (delta : ENNReal) ^ (-coverExponent) := by
  apply stickyDensityAwareCoverLoss_le_of_cardScaleMass
    S A ((delta : ENNReal) ^ (-coverExponent))
      hdelta hactive hrhoHalf
  exact scaledCoverCost_of_powerEnvelopes hdelta hdeltaOne
    habsorbExponent hdeltaSmall hA hX hsourceMass hexponent

#print axioms densityAwareCoverLossThreshold
#print axioms densityAwareCoverLossThreshold_pos
#print axioms scaledCoverCost_of_powerEnvelopes
#print axioms stickyDensityAwareCoverLoss_le_rpow_of_powerEnvelopes

end
end Family8StickyDensityAwareCoverLossPowerEnvelopeV1
