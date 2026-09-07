import Family8Grounding.Family8StickyKatzTaoBoundedFiberPartitionV4
import Family8Grounding.Family8KatzTaoDoubledFiberRelativePowerEnvelopeV4
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1
import Mathlib.Tactic

/-!
# Dual count powers from one active restricted fibre cap, V3

V1 and V2 failed only at coercion side conditions and are not imported.  The literal doubled-fibre Katz--Tao cap simultaneously controls the full
selected-parent fibre at the relative scale and at the normalized
contracted-John proxy scale.  Thus downstream consumers use one cap and one
parent, rather than unrelated cardinality estimates.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveRestrictedFiberDualCountPowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open Family8KatzTaoDoubledFiberRelativePowerEnvelopeV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- One literal active restricted fibre satisfies both count estimates needed
by the fresh low-CF long-middle endpoint. -/
theorem activeRestrictedFiber_fullCard_proxyPower_and_relativeCount
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {CKT : ENNReal} (hCKTone : 1 ≤ CKT) (hCKTfinite : CKT ≠ ∞)
    (hKT : IsKatzTao CKT fine.bodyFamily)
    (q : {q // q ∈ (activeFineRestrictedScaleCover S).activeCoarse})
    {kappa absorbExp : Real}
    (hcountExp : 0 < 2 + kappa) (habsorbExp : 0 < absorbExp)
    (hCKTratio : CKT ≤
      (((delta : ENNReal) / (rho : ENNReal)) ^ (-kappa)))
    (hsmall : contractedJohnProxyRadius delta rho / 8 ≤
      finiteConstantSmallDeltaThreshold
        ordinaryFiberNatCapFixedConstant absorbExp) :
    (Fintype.card
        {i // i ∈ (activeFineRestrictedScaleCover S).fiber q.1} : ENNReal) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 + kappa + absorbExp))) ∧
      (Fintype.card
        {i // i ∈ (activeFineRestrictedScaleCover S).fiber q.1} : ENNReal) ≤
        ordinaryFiberNatCapFixedConstant *
          (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))) := by
  let U := activeFineRestrictedScaleCover S
  let M := Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
    delta rho CKT
  let ratio : ENNReal := (delta : ENNReal) / (rho : ENNReal)
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  have hcardNat : (U.fiber q.1).card ≤ M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      S hdelta hdeltaHalf hrhoOne hCKTfinite hKT q.1 q.2
  have hcardNat' : Fintype.card {i // i ∈ U.fiber q.1} ≤ M := by
    simpa only [Fintype.card_coe] using hcardNat
  have hcardM :
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) ≤ (M : ENNReal) := by
    exact_mod_cast hcardNat'
  have hMrelative : (M : ENNReal) ≤
      ordinaryFiberNatCapFixedConstant * ratio ^ (-(2 + kappa)) := by
    simpa only [M, ratio] using
      (katzTaoDoubledFiberNatCap_le_fixed_mul_ratio_negativePower
        hdelta hdeltaRho hCKTone hCKTfinite hCKTratio)
  have hrelative :
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) ≤
        ordinaryFiberNatCapFixedConstant * ratio ^ (-(2 + kappa)) :=
    hcardM.trans hMrelative
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hfixed : ordinaryFiberNatCapFixedConstant ≤
      (scale : ENNReal) ^ (-absorbExp) :=
    finiteConstant_le_delta_negativePower
      ordinaryFiberNatCapFixedConstant_ne_top habsorbExp hscalePos hsmall
  have hfixedOne : (3 / 64 : ENNReal) ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num
  have hfixedRatio : (1 : ENNReal) ≤
      (3 / 64 : ENNReal) ^ (-(2 + kappa)) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (by norm_num) hfixedOne (by linarith)
  have hratioScale : ratio ^ (-(2 + kappa)) ≤
      (scale : ENNReal) ^ (-(2 + kappa)) := by
    calc
      ratio ^ (-(2 + kappa)) =
          1 * ratio ^ (-(2 + kappa)) := by rw [one_mul]
      _ ≤ (3 / 64 : ENNReal) ^ (-(2 + kappa)) *
          ratio ^ (-(2 + kappa)) := mul_le_mul' hfixedRatio le_rfl
      _ = (scale : ENNReal) ^ (-(2 + kappa)) := by
        simpa only [scale, ratio] using
          (contractedJohnProxyRadius_div_eight_rpow_eq
            (delta := delta) hrho (-(2 + kappa))).symm
  have hscale0 : (scale : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hscalePos.ne'
  have hscaleTop : (scale : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hproxy :
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) ≤
        (scale : ENNReal) ^ (-(2 + kappa + absorbExp)) := by
    calc
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) ≤
          ordinaryFiberNatCapFixedConstant * ratio ^ (-(2 + kappa)) :=
        hrelative
      _ ≤ (scale : ENNReal) ^ (-absorbExp) *
          (scale : ENNReal) ^ (-(2 + kappa)) :=
        mul_le_mul' hfixed hratioScale
      _ = (scale : ENNReal) ^ (-(2 + kappa + absorbExp)) := by
        rw [show -(2 + kappa + absorbExp) =
            -absorbExp + -(2 + kappa) by ring,
          ENNReal.rpow_add _ _ hscale0 hscaleTop]
  exact ⟨by simpa only [U, scale] using hproxy,
    by simpa only [U, ratio] using hrelative⟩

#print axioms activeRestrictedFiber_fullCard_proxyPower_and_relativeCount

end
end Family8StickyActiveRestrictedFiberDualCountPowerV3
