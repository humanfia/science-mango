import Family8Grounding.Family8StickySelectedFiberLowCFScalarEnvelopeV4
import Family8Grounding.Family8StickyFiberContractedJohnSourcePowerEndpointV1
import Mathlib.Tactic

/-!
# Power budgets for the selected low-CF strict middle endpoint, V2

V1 omitted the namespace exporting the unit-ball body.  This corrected successor replaces the literal normalized-proxy density and base budgets by
three source-side power comparisons: a card-envelope power, a retained source
density power, and a full-fibre card-volume base power.  The genuine density
transport and the normalized Katz--Tao card envelope are applied internally.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFPowerBudgetsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyFiberContractedJohnDensityTransportV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Source-side power comparisons produce all three literal scalar budgets
consumed by the selected low-CF strict middle theorem. -/
theorem selectedFiberLowCF_density_base_loss_budgets
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower L : ENNReal)
    {eta p a : Real}
    (hp : 0 < p) (ha : 0 < a)
    (hsmall : contractedJohnProxyRadius delta rho / 8 ≤
      contractedJohnSourcePowerEndpointThreshold a)
    (hcardEnvelopePower :
      selectedFiberLowCFCardEnvelope S q selected lower L ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-p)))
    (hsourceDensityPower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) ≤
        (((stickyFiberSourceShading S Y q.1).shadingDensity / 93312 / 128) /
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-(p + a)))))
    (hbasePower :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 * p + a))) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-eta)) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              2 / 2))) :
    let loss := stickyFiberContractedJohnSourceClosedLoss
      (selectedFiberLowCFCardEnvelope S q selected lower L)
    let normalizedC :=
      128 * stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne q
          (selectedFiberLowCFSourceConstant S q selected lower L)
    (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) ≤
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne q)).shading.shadingDensity / loss ∧
      loss * (normalizedC * volume (unitBallBody : Set Space)) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-eta)) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              2 / 2)) ∧
      loss ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(p + a))) := by
  dsimp only
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  let Cenv := selectedFiberLowCFCardEnvelope S q selected lower L
  let loss := stickyFiberContractedJohnSourceClosedLoss Cenv
  let normalizedC :=
    128 * stickyFiberContractedJohnProxyKatzTaoConstant
      S hrho hrhoOne q
        (selectedFiberLowCFSourceConstant S q selected lower L)
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hproxyHalf : contractedJohnProxyRadius delta rho ≤ (2 : NNReal)⁻¹ :=
    stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho
  have hscaleOne : scale ≤ 1 := by
    dsimp only [scale]
    calc
      contractedJohnProxyRadius delta rho / 8 ≤
          (2 : NNReal)⁻¹ / 8 := by gcongr
      _ ≤ 1 := by
        rw [← NNReal.coe_le_coe]
        norm_num
  have hsmallLoss : scale ≤ contractedJohnSourceClosedLossThreshold a :=
    hsmall.trans (min_le_left _ _)
  have hsmallBase : scale ≤ contractedJohnSourceBaseThreshold a :=
    hsmall.trans (min_le_right _ _)
  have hCenvPower : Cenv ≤ (scale : ENNReal) ^ (-p) := by
    simpa only [Cenv, scale] using hcardEnvelopePower
  have hloss : loss ≤ (scale : ENNReal) ^ (-(p + a)) := by
    dsimp only [loss]
    exact stickyFiberContractedJohnSourceClosedLoss_le_negativePower
      hscalePos hscaleOne hp ha hsmallLoss hCenvPower
  have hnormalizedC : normalizedC ≤ 128 * (93312 * Cenv) := by
    dsimp only [normalizedC, Cenv]
    exact selectedFiberLowCF_normalizedConstant_le_cardEnvelope
      S hdelta hrho hrhoOne q selected lower L
  have hbaseEnvelope :
      loss * ((128 * (93312 * Cenv)) *
          volume (unitBallBody : Set Space)) ≤
        (scale : ENNReal) ^ (-(2 * p + a)) := by
    dsimp only [loss]
    exact stickyFiberContractedJohnSourceBase_le_negativePower
      hscalePos hscaleOne hp ha hsmallBase hCenvPower
  have hbase :
      loss * (normalizedC * volume (unitBallBody : Set Space)) ≤
        (scale : ENNReal) ^ (-eta) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            ((scale : ENNReal) ^ 2 / 2)) := by
    calc
      loss * (normalizedC * volume (unitBallBody : Set Space)) ≤
          loss * ((128 * (93312 * Cenv)) *
            volume (unitBallBody : Set Space)) := by gcongr
      _ ≤ (scale : ENNReal) ^ (-(2 * p + a)) := hbaseEnvelope
      _ ≤ (scale : ENNReal) ^ (-eta) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            ((scale : ENNReal) ^ 2 / 2)) := by
        simpa only [scale] using hbasePower
  have htransport :
      (stickyFiberSourceShading S Y q.1).shadingDensity / 93312 / 128 ≤
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne q)).shading.shadingDensity :=
    stickyFiberSource_shadingDensity_div_93312_div_128_le_normalizedProxy
      S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho q
  have hdensity : (scale : ENNReal) ^ eta ≤
      (eighthNormalizedDatum
        (stickyFiberContractedJohnProxyDatum
          S Y hrho hrhoOne q)).shading.shadingDensity / loss := by
    calc
      (scale : ENNReal) ^ eta ≤
          ((stickyFiberSourceShading S Y q.1).shadingDensity / 93312 / 128) /
            (scale : ENNReal) ^ (-(p + a)) := by
        simpa only [scale] using hsourceDensityPower
      _ ≤ ((stickyFiberSourceShading S Y q.1).shadingDensity / 93312 / 128) /
          loss := ENNReal.div_le_div_left hloss _
      _ ≤ (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne q)).shading.shadingDensity / loss :=
        ENNReal.div_le_div_right htransport loss
  refine ⟨?_, ?_, ?_⟩
  · simpa only [scale, loss] using hdensity
  · simpa only [scale, loss, normalizedC] using hbase
  · simpa only [scale, loss] using hloss

#print axioms selectedFiberLowCF_density_base_loss_budgets

end
end Family8StickySelectedFiberLowCFPowerBudgetsV2
