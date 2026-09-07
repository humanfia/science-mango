import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Family8Grounding.Family8CommonPointTubePackingV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Automatic source Katz--Tao hypotheses from Frostman control and packing

Ambient Frostman control gives a global Katz--Tao constant equal to the
Frostman constant times the actual family-volume density.  Common-point
packing bounds that density by a fixed constant times `delta ^ (-2)`.
Consequently an arbitrary positive reserve absorbs the fixed constant and
produces the honest source exponent `outputEta + 2 + absorbEta`.

The exponent-two packing cost is kept explicit: this module does not present
it as a harmless fixed coefficient.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SourceKatzTaoHypothesesFromFrostmanPackingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8AmbientFamilyVolumeDensityV2
open Family8CommonPointTubePackingV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- Terminal scale for the geometric packing theorem and absorption of its
finite numerical constant. -/
def sourceKatzTaoFromFrostmanPackingThreshold
    (absorbEta : Real) : NNReal :=
  min (1 / 100 : NNReal)
    (finiteConstantSmallDeltaThreshold
      commonPointTubePackingConstant absorbEta)

theorem sourceKatzTaoFromFrostmanPackingThreshold_pos
    (absorbEta : Real) :
    0 < sourceKatzTaoFromFrostmanPackingThreshold absorbEta := by
  rw [sourceKatzTaoFromFrostmanPackingThreshold, lt_min_iff]
  exact ⟨by positivity,
    finiteConstantSmallDeltaThreshold_pos _ _⟩

/-- Common-point packing, divided by the volume of the unit ball, bounds the
literal ambient family-volume density. -/
theorem ambientFamilyVolumeDensity_le_commonPointPacking
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    ambientFamilyVolumeDensity D.family.bodyFamily unitBallBody <=
      commonPointTubePackingConstant *
        (delta : ENNReal) ^ (-2 : Real) := by
  have hunitOne :
      (1 : ENNReal) <= volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hunit0 : volume (unitBallBody : Set Space) ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ENNReal) < 1).trans_le hunitOne)
  have hunitTop : volume (unitBallBody : Set Space) ≠ ∞ :=
    unitBallBody.isCompact.measure_lt_top.ne
  have hvolume : familyVolume D.family.bodyFamily <=
      (commonPointTubePackingConstant *
          volume (unitBallBody : Set Space)) *
        (delta : ENNReal) ^ (-2 : Real) := by
    simpa only [ActualTubeDatum.actualFamilyVolume,
      commonPointFamilyVolumeConstant] using
        actualFamilyVolume_le_commonPointPacking D hD hdeltaSmall
  unfold ambientFamilyVolumeDensity
  apply (ENNReal.div_le_iff hunit0 hunitTop).2
  calc
    familyVolume D.family.bodyFamily <=
        (commonPointTubePackingConstant *
            volume (unitBallBody : Set Space)) *
          (delta : ENNReal) ^ (-2 : Real) := hvolume
    _ = (commonPointTubePackingConstant *
          (delta : ENNReal) ^ (-2 : Real)) *
        volume (unitBallBody : Set Space) := by ac_rfl

/-- A literal Frostman datum automatically supplies the source Katz--Tao
hypotheses used by the source-average route.  The only small-scale inputs are
the proved geometric packing range and absorption of a finite constant. -/
theorem katzTaoHypotheses_of_frostman_commonPointPacking
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {outputEta absorbEta : Real}
    (habsorbEta : 0 < absorbEta)
    (hdelta : delta <=
      sourceKatzTaoFromFrostmanPackingThreshold absorbEta)
    (hF : FrostmanHypotheses D outputEta) :
    KatzTaoHypotheses D (outputEta + 2 + absorbEta) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  have hdeltaGeometric : delta <= (1 / 100 : NNReal) :=
    hdelta.trans (min_le_left _ _)
  have hdeltaAbsorb : delta <=
      finiteConstantSmallDeltaThreshold
        commonPointTubePackingConstant absorbEta :=
    hdelta.trans (min_le_right _ _)
  have hconstant : commonPointTubePackingConstant <=
      (delta : ENNReal) ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      commonPointTubePackingConstant_ne_top habsorbEta hD.delta_pos
        hdeltaAbsorb
  have hdensity :
      ambientFamilyVolumeDensity D.family.bodyFamily unitBallBody <=
        commonPointTubePackingConstant *
          (delta : ENNReal) ^ (-2 : Real) :=
    ambientFamilyVolumeDensity_le_commonPointPacking
      D hD hdeltaGeometric
  have hunitOne :
      (1 : ENNReal) <= volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hunit0 : volume (unitBallBody : Set Space) ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ENNReal) < 1).trans_le hunitOne)
  have hunitTop : volume (unitBallBody : Set Space) ≠ ∞ :=
    unitBallBody.isCompact.measure_lt_top.ne
  have hsourceKT : IsKatzTao
      ((delta : ENNReal) ^ (-outputEta) *
        ambientFamilyVolumeDensity D.family.bodyFamily unitBallBody)
      D.family.bodyFamily :=
    isKatzTao_of_isFrostmanIn_familyVolumeDensity
      hF.2 hunit0 hunitTop
  have hcoefficient :
      (delta : ENNReal) ^ (-outputEta) *
          ambientFamilyVolumeDensity D.family.bodyFamily unitBallBody <=
        (delta : ENNReal) ^ (-(outputEta + 2 + absorbEta)) := by
    calc
      (delta : ENNReal) ^ (-outputEta) *
          ambientFamilyVolumeDensity D.family.bodyFamily unitBallBody <=
        (delta : ENNReal) ^ (-outputEta) *
          (commonPointTubePackingConstant *
            (delta : ENNReal) ^ (-2 : Real)) :=
          mul_le_mul_right hdensity _
      _ <= (delta : ENNReal) ^ (-outputEta) *
          ((delta : ENNReal) ^ (-absorbEta) *
            (delta : ENNReal) ^ (-2 : Real)) := by
          exact mul_le_mul_right (mul_le_mul_left hconstant _) _
      _ = (delta : ENNReal) ^ (-(outputEta + 2 + absorbEta)) := by
        rw [← ENNReal.rpow_add (-absorbEta) (-2 : Real) hd0 hdTop,
          ← ENNReal.rpow_add (-outputEta)
            (-absorbEta + (-2 : Real)) hd0 hdTop]
        congr 1
        ring
  rw [katzTaoHypotheses_iff_density_and_isKatzTao]
  constructor
  · exact
      (ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)).trans hF.1
  · rw [← maximalConcentration_le_iff_isKatzTao]
    exact (maximalConcentration_le_iff_isKatzTao.mpr hsourceKT).trans
      hcoefficient

#print axioms sourceKatzTaoFromFrostmanPackingThreshold
#print axioms sourceKatzTaoFromFrostmanPackingThreshold_pos
#print axioms ambientFamilyVolumeDensity_le_commonPointPacking
#print axioms katzTaoHypotheses_of_frostman_commonPointPacking

end
end Family8SourceKatzTaoHypothesesFromFrostmanPackingV1
