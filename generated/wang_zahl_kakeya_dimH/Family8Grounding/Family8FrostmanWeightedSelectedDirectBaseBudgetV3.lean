import Family8Grounding.Family8DoubledParentConflictWeightedShadingMassBridgeV2
import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
import Family8Grounding.Family8KatzTaoDoubledParentConflictBudgetSideConditionsV1
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8UnitBallBodyVolumeUpperV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrostmanWeightedSelectedDirectBaseBudgetV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open Family8KatzTaoDoubledParentConflictBudgetSideConditionsV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8UnitBallBodyVolumeUpperV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Direct source-Frostman mass to selected-family base budget

This connector does not count parents and does not mention a long-interval
scalar `X`.  It uses the literal source Frostman shading-mass lower bound,
the literal weighted selected restriction, and the exact conflict-degree
envelope.  The sole extra constant is the finite unit-ball volume, absorbed
below an explicit threshold.
-/

/-- Loss paid in addition to the two source-Frostman density exponents. -/
def directSelectedBasePowerLoss
    (epsilon katzTaoExponent degreeAbsorbExponent
      volumeAbsorbExponent : Real) : Real :=
  activeOwnerExactDegreePowerEnvelope
      epsilon katzTaoExponent degreeAbsorbExponent +
    katzTaoExponent + volumeAbsorbExponent

theorem directSelectedBasePowerLoss_eq
    (epsilon katzTaoExponent degreeAbsorbExponent
      volumeAbsorbExponent : Real) :
    directSelectedBasePowerLoss epsilon katzTaoExponent
        degreeAbsorbExponent volumeAbsorbExponent =
      3 * katzTaoExponent + 4 * epsilon +
        degreeAbsorbExponent + volumeAbsorbExponent := by
  unfold directSelectedBasePowerLoss activeOwnerExactDegreePowerEnvelope
  ring

/-- Explicit threshold absorbing the rational upper bound eight for the
ambient unit-ball volume. -/
def directSelectedBaseVolumeSmallDeltaThreshold
    (volumeAbsorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 8 volumeAbsorbExponent

theorem directSelectedBaseVolumeSmallDeltaThreshold_pos
    (volumeAbsorbExponent : Real) :
    0 < directSelectedBaseVolumeSmallDeltaThreshold volumeAbsorbExponent :=
  finiteConstantSmallDeltaThreshold_pos 8 volumeAbsorbExponent

theorem volume_unitBallBody_le_negativePower
    {delta : NNReal} {volumeAbsorbExponent : Real}
    (hdelta : 0 < delta) (habsorb : 0 < volumeAbsorbExponent)
    (hdeltaThreshold :
      delta <= directSelectedBaseVolumeSmallDeltaThreshold
        volumeAbsorbExponent) :
    volume (unitBallBody : Set Space) <=
      (delta : ENNReal) ^ (-volumeAbsorbExponent) := by
  exact volume_unitBallBody_le_eight.trans
    (finiteConstant_le_delta_negativePower
      (by norm_num : (8 : ENNReal) ≠ ⊤) habsorb hdelta
      hdeltaThreshold)

namespace ScaleCover

/-- Canonical direct selected-volume base budget.  All mass input comes from
the actual source Frostman datum and all selection input from the actual
weighted restriction.  There is no cardinal, fibre-cap, `X`, or equivalent
scalar callback. -/
theorem canonicalLowerBufferedScale_weightedSelected_baseBudget_of_frostman
    {tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum tau index) (hD : D.IsAdmissible)
    {sourceExponent : Real} (hF : FrostmanHypotheses D sourceExponent)
    {A : ENNReal}
    {epsilon katzTaoExponent degreeAbsorbExponent
      volumeAbsorbExponent targetExponent : Real}
    {S : StickyScaleCover D.family
      (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
        tau theta epsilon)}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading)
      (katzTaoDoubledParentConflictBudget tau
        (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
          tau theta epsilon) A))
    (hactive : S.activeFine = Finset.univ)
    (htauTheta : tau <= theta) (hthetaOne : theta <= 1)
    (hepsilon : 0 <= epsilon)
    (hdegreeAbsorb : 0 < degreeAbsorbExponent)
    (hvolumeAbsorb : 0 < volumeAbsorbExponent)
    (htauDegreeThreshold :
      tau <= activeOwnerExactDegreeSmallDeltaThreshold degreeAbsorbExponent)
    (htauVolumeThreshold :
      tau <= directSelectedBaseVolumeSmallDeltaThreshold
        volumeAbsorbExponent)
    (hAone : 1 <= A)
    (hA : A <= (tau : ENNReal) ^ (-katzTaoExponent))
    (hexponent :
      2 * sourceExponent +
          directSelectedBasePowerLoss epsilon katzTaoExponent
            degreeAbsorbExponent volumeAbsorbExponent <= targetExponent) :
    A * volume (unitBallBody : Set Space) <=
      (tau : ENNReal) ^ (-targetExponent) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  let B := katzTaoDoubledParentConflictBudget tau
    (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
      tau theta epsilon) A
  let selected := restrictActualTubeDatum D
    (weightedSelectedFineIndices D.shading W)
  have htauOne : tau <= 1 := htauTheta.trans hthetaOne
  have hd0 : (tau : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (tau : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdOneENN : (tau : ENNReal) <= 1 := by
    exact_mod_cast htauOne
  have hB0 : B ≠ 0 :=
    katzTaoDoubledParentConflictBudget_ne_zero tau
      (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
        tau theta epsilon) A
  have hBTop : B ≠ ⊤ :=
    katzTaoDoubledParentConflictBudget_ne_top tau
      (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale
        tau theta epsilon) A
  have hB : B <= (tau : ENNReal) ^
      (-activeOwnerExactDegreePowerEnvelope epsilon katzTaoExponent
        degreeAbsorbExponent) := by
    simpa only [B, katzTaoDoubledParentConflictBudget] using
      (canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope_auto
        (globalDelta := tau) (tau := tau) (theta := theta) (A := A)
        (epsilon := epsilon) (eta := katzTaoExponent)
        (absorbEta := degreeAbsorbExponent)
        hD.delta_pos le_rfl htauTheta hthetaOne hepsilon hdegreeAbsorb
        htauDegreeThreshold hAone hA)
  have hvolume : volume (unitBallBody : Set Space) <=
      (tau : ENNReal) ^ (-volumeAbsorbExponent) :=
    volume_unitBallBody_le_negativePower hD.delta_pos hvolumeAbsorb
      htauVolumeThreshold
  have hmass : (tau : ENNReal) ^ (2 * sourceExponent) <=
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  have hretained : D.shading.shadingMass <=
      B * selected.shading.shadingMass := by
    exact source_shadingMass_le_mul_weightedSelected_shadingMass
      D W hactive
  have hselectedMass : selected.shading.shadingMass <=
      selected.actualFamilyVolume := by
    exact selected.shading.shadingMass_le_familyVolume
  have hexponent' :
      2 * sourceExponent +
          activeOwnerExactDegreePowerEnvelope epsilon katzTaoExponent
            degreeAbsorbExponent + katzTaoExponent +
            volumeAbsorbExponent <= targetExponent := by
    unfold directSelectedBasePowerLoss at hexponent
    linarith
  apply (ENNReal.mul_le_mul_iff_right hB0 hBTop).mp
  calc
    B * (A * volume (unitBallBody : Set Space)) <=
        (tau : ENNReal) ^
            (-activeOwnerExactDegreePowerEnvelope epsilon katzTaoExponent
              degreeAbsorbExponent) *
          ((tau : ENNReal) ^ (-katzTaoExponent) *
            (tau : ENNReal) ^ (-volumeAbsorbExponent)) := by
      exact mul_le_mul hB (mul_le_mul hA hvolume bot_le bot_le) bot_le bot_le
    _ = (tau : ENNReal) ^
        (-(activeOwnerExactDegreePowerEnvelope epsilon katzTaoExponent
            degreeAbsorbExponent + katzTaoExponent +
              volumeAbsorbExponent)) := by
      rw [show -(activeOwnerExactDegreePowerEnvelope epsilon katzTaoExponent
          degreeAbsorbExponent + katzTaoExponent +
            volumeAbsorbExponent) =
        (-activeOwnerExactDegreePowerEnvelope epsilon katzTaoExponent
          degreeAbsorbExponent) +
          ((-katzTaoExponent) + (-volumeAbsorbExponent)) by ring,
        ENNReal.rpow_add _ _ hd0 hdTop,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (tau : ENNReal) ^
        (2 * sourceExponent - targetExponent) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN
      linarith
    _ = (tau : ENNReal) ^ (-targetExponent) *
        (tau : ENNReal) ^ (2 * sourceExponent) := by
      rw [show 2 * sourceExponent - targetExponent =
        -targetExponent + 2 * sourceExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (tau : ENNReal) ^ (-targetExponent) *
        D.shading.shadingMass := mul_le_mul' le_rfl hmass
    _ <= (tau : ENNReal) ^ (-targetExponent) *
        (B * selected.shading.shadingMass) :=
      mul_le_mul' le_rfl hretained
    _ <= (tau : ENNReal) ^ (-targetExponent) *
        (B * selected.actualFamilyVolume) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hselectedMass)
    _ = B * ((tau : ENNReal) ^ (-targetExponent) *
        selected.actualFamilyVolume) := by
      ac_rfl

#print axioms directSelectedBasePowerLoss_eq
#print axioms directSelectedBaseVolumeSmallDeltaThreshold_pos
#print axioms volume_unitBallBody_le_negativePower
#print axioms
  canonicalLowerBufferedScale_weightedSelected_baseBudget_of_frostman

end ScaleCover
end
end Family8FrostmanWeightedSelectedDirectBaseBudgetV3
