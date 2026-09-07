import Family8Grounding.Family8StickySelectedFiberLowCFFreshRetentionProducerV2
import Family8Grounding.Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
import Mathlib.Tactic

/-!
# Automatic power bound for the fresh low-CF card envelope, V3

V1 omitted the nested-scale premise and V2 failed only in the final rpow reassociation; neither is imported.  The full low-CF Katz--Tao constant is bounded by `lower * fullCard`.  Hence
the genuine fresh loss costs one copy of the combined lower/card exponent.
After using `selected.card <= fullCard`, the final selected card envelope
costs two copies of each exponent plus fixed small-power absorptions.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnAffineJacobianLowerV3
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def selectedParentLowCFFreshCardEnvelopePowerThreshold
    (a absorbExp : Real) : NNReal :=
  min (contractedJohnSourceClosedLossThreshold a)
    (finiteConstantSmallDeltaThreshold 16 absorbExp)

theorem selectedParentLowCFFreshCardEnvelopePowerThreshold_pos
    (a absorbExp : Real) :
    0 < selectedParentLowCFFreshCardEnvelopePowerThreshold a absorbExp :=
  lt_min (contractedJohnSourceClosedLossThreshold_pos a)
    (finiteConstantSmallDeltaThreshold_pos 16 absorbExp)

/-- Lower-barrier and full-fibre-card power bounds automatically control the
literal card envelope for every selected subtype produced by the genuine
fresh selector. -/
theorem selectedParentLowCFFresh_cardEnvelope_le_power
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower : ENNReal} {lowerExp cardExp a absorbExp : Real}
    (hcombined : 0 < lowerExp + cardExp)
    (ha : 0 < a) (habsorbExp : 0 < absorbExp)
    (hsmall : contractedJohnProxyRadius delta rho / 8 ≤
      selectedParentLowCFFreshCardEnvelopePowerThreshold a absorbExp)
    (hlower : lower ≤
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
        (-lowerExp)))
    (hfullCard :
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-cardExp))) :
    selectedFiberLowCFCardEnvelope S q selected lower
        (selectedParentLowCFFreshLoss S hrho hrhoOne q lower) ≤
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
        (-(2 * lowerExp + 2 * cardExp + a + absorbExp))) := by
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  let sourceC := selectedParentLowCFFullSourceConstant S q lower
  let proxyC := selectedParentLowCFFullProxyConstant
    S hrho hrhoOne q lower
  let freshLoss := selectedParentLowCFFreshLoss S hrho hrhoOne q lower
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hscaleOne : scale ≤ 1 := by
    dsimp only [scale]
    have hproxyHalf : contractedJohnProxyRadius delta rho ≤ (2 : NNReal)⁻¹ :=
      stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho
    calc
      contractedJohnProxyRadius delta rho / 8 ≤
          (2 : NNReal)⁻¹ / 8 := by gcongr
      _ ≤ 1 := by
        rw [← NNReal.coe_le_coe]
        norm_num
  have hparent0 : volume (S.activeCoarseFamily q : Set Space) ≠ 0 := by
    change volume (S.coarse.tubes q.1).carrier ≠ 0
    exact (Tube.volume_pos (S.coarse.tubes q.1) hrho).ne'
  have hdensityCard :
      ambientFamilyVolumeDensity
          (S.fiberFamily q.1) (S.activeCoarseFamily q) ≤
        (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) := by
    apply ambientFamilyVolumeDensity_le_card
    · intro i
      exact fiberFamily_subset_parent S q i
    · exact hparent0
  have hscale0 : (scale : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hscalePos.ne'
  have hscaleTop : (scale : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hsourceCPower : sourceC ≤
      (scale : ENNReal) ^ (-(lowerExp + cardExp)) := by
    calc
      sourceC ≤ lower *
          (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) := by
        dsimp only [sourceC, selectedParentLowCFFullSourceConstant]
        exact mul_le_mul' le_rfl hdensityCard
      _ ≤ (scale : ENNReal) ^ (-lowerExp) *
          (scale : ENNReal) ^ (-cardExp) := by
        exact mul_le_mul' (by simpa only [scale] using hlower)
          (by simpa only [scale] using hfullCard)
      _ = (scale : ENNReal) ^ (-(lowerExp + cardExp)) := by
        rw [show -(lowerExp + cardExp) = -lowerExp + -cardExp by ring,
          ENNReal.rpow_add _ _ hscale0 hscaleTop]
  have hproxyEnvelope : proxyC ≤ 93312 * sourceC := by
    simpa only [proxyC, selectedParentLowCFFullProxyConstant] using
      (stickyFiberContractedJohnProxyKatzTaoConstant_le_fixed
        S hdelta hrho hrhoOne q sourceC)
  have hfreshSourceLoss : freshLoss ≤
      stickyFiberContractedJohnSourceClosedLoss sourceC := by
    dsimp only [freshLoss, selectedParentLowCFFreshLoss]
    unfold stickyFiberContractedJohnSourceClosedLoss
    exact add_le_add
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hproxyEnvelope)) le_rfl
  have hsmallLoss : scale ≤ contractedJohnSourceClosedLossThreshold a :=
    hsmall.trans (min_le_left _ _)
  have hfreshPower : freshLoss ≤
      (scale : ENNReal) ^ (-((lowerExp + cardExp) + a)) :=
    hfreshSourceLoss.trans
      (stickyFiberContractedJohnSourceClosedLoss_le_negativePower
        hscalePos hscaleOne hcombined ha hsmallLoss hsourceCPower)
  have hselectedCard : (selected.card : ENNReal) ≤
      (scale : ENNReal) ^ (-cardExp) := by
    calc
      (selected.card : ENNReal) ≤
          (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) := by
        exact_mod_cast (Finset.card_le_univ selected)
      _ ≤ (scale : ENNReal) ^ (-cardExp) := by
        simpa only [scale] using hfullCard
  have hsmallSixteen : scale ≤
      finiteConstantSmallDeltaThreshold 16 absorbExp :=
    hsmall.trans (min_le_right _ _)
  have hsixteen : (16 : ENNReal) ≤
      (scale : ENNReal) ^ (-absorbExp) :=
    finiteConstant_le_delta_negativePower
      (by norm_num) habsorbExp hscalePos hsmallSixteen
  calc
    selectedFiberLowCFCardEnvelope S q selected lower
        (selectedParentLowCFFreshLoss S hrho hrhoOne q lower) =
        lower * (16 * freshLoss) * (selected.card : ENNReal) := by
      rfl
    _ ≤ (scale : ENNReal) ^ (-lowerExp) *
        ((scale : ENNReal) ^ (-absorbExp) *
          (scale : ENNReal) ^ (-((lowerExp + cardExp) + a))) *
        (scale : ENNReal) ^ (-cardExp) := by
      exact mul_le_mul'
        (mul_le_mul' (by simpa only [scale] using hlower)
          (mul_le_mul' hsixteen hfreshPower)) hselectedCard
    _ = (scale : ENNReal) ^
        (-(2 * lowerExp + 2 * cardExp + a + absorbExp)) := by
      calc
        (scale : ENNReal) ^ (-lowerExp) *
            ((scale : ENNReal) ^ (-absorbExp) *
              (scale : ENNReal) ^ (-((lowerExp + cardExp) + a))) *
            (scale : ENNReal) ^ (-cardExp) =
            (((scale : ENNReal) ^ (-lowerExp) *
                (scale : ENNReal) ^ (-absorbExp)) *
              (scale : ENNReal) ^ (-((lowerExp + cardExp) + a))) *
              (scale : ENNReal) ^ (-cardExp) := by ac_rfl
        _ = (((scale : ENNReal) ^ (-lowerExp + -absorbExp)) *
              (scale : ENNReal) ^ (-((lowerExp + cardExp) + a))) *
              (scale : ENNReal) ^ (-cardExp) := by
            rw [← ENNReal.rpow_add _ _ hscale0 hscaleTop]
        _ = ((scale : ENNReal) ^
              ((-lowerExp + -absorbExp) +
                -((lowerExp + cardExp) + a))) *
              (scale : ENNReal) ^ (-cardExp) := by
            rw [← ENNReal.rpow_add _ _ hscale0 hscaleTop]
        _ = (scale : ENNReal) ^
              (((-lowerExp + -absorbExp) +
                -((lowerExp + cardExp) + a)) + -cardExp) := by
            rw [← ENNReal.rpow_add _ _ hscale0 hscaleTop]
        _ = (scale : ENNReal) ^
            (-(2 * lowerExp + 2 * cardExp + a + absorbExp)) := by
          congr 1
          ring

#print axioms selectedParentLowCFFreshCardEnvelopePowerThreshold
#print axioms selectedParentLowCFFreshCardEnvelopePowerThreshold_pos
#print axioms selectedParentLowCFFresh_cardEnvelope_le_power

end
end Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3
