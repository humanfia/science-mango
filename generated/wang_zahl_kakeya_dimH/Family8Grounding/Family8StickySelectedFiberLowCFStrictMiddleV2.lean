import Family8Grounding.Family8ENNRealLossStrictMiddleCompositionV2
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Family8Grounding.Family8StickySelectedFiberLowCFScalarEnvelopeV4
import Family8Grounding.Family8StickySelectedFiberContractedJohnNormalizedKatzTaoV1
import Mathlib.Tactic

/-!
# Strict middle bound on the literal retained low-CF Sticky fibre, V2

V1 omitted the proxy-scale-ratio import and rewrote through a local datum alias too aggressively.  This corrected successor keeps the selected parent and selected child set fixed by the caller.  A local
Frostman certificate produces Katz--Tao control on that same subtype.  Its
contracted-John normalization is then consumed with the honest closed
card-envelope loss.  Density, base, loss-power, count-power, and final
absorption budgets are displayed explicitly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberLowCFStrictMiddleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open Family8ENNRealLossStrictMiddleCompositionV2
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickySelectedFiberContractedJohnNormalizedKatzTaoV1
open Family8StickySelectedFiberLocalFrostmanKatzTaoV1
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho globalDelta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The low-CF branch reaches the exact strict middle estimate on its same
selected fibre.  The retained cardinality is the literal middle count. -/
theorem four_mul_selectedFiberSourceAverage_le_strictMiddle
    {frostmanBeta frostmanEpsilon frostmanEta gamma : Real}
    {lossExp kappa globalEta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower L : ENNReal}
    (hlowerTop : lower ≠ ∞) (hLTop : L ≠ ∞)
    (hLow : IsFrostmanIn (lower * (16 * L))
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q))
    (K : ENNReal)
    (hdelta0 : contractedJohnProxyRadius delta rho / 8 ≤ delta0)
    (hadmissible :
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne q)) selected).IsAdmissible)
    (hcard :
      (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) ≤
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower L) *
          (selected.card : ENNReal))
    (hmass :
      (eighthNormalizedDatum
        (stickyFiberContractedJohnProxyDatum
          S Y hrho hrhoOne q)).shading.shadingMass ≤
        stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower L) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne q)) selected).shading.shadingMass)
    (hdensityBudget :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          frostmanEta) ≤
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne q)).shading.shadingDensity /
          stickyFiberContractedJohnSourceClosedLoss
            (selectedFiberLowCFCardEnvelope S q selected lower L))
    (hbaseBudget :
      stickyFiberContractedJohnSourceClosedLoss
          (selectedFiberLowCFCardEnvelope S q selected lower L) *
        ((128 * stickyFiberContractedJohnProxyKatzTaoConstant
            S hrho hrhoOne q
              (selectedFiberLowCFSourceConstant
                S q selected lower L)) *
          volume (unitBallBody : Set Space)) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-frostmanEta)) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              2 / 2)))
    (hlossPower :
      stickyFiberContractedJohnSourceClosedLoss
          (selectedFiberLowCFCardEnvelope S q selected lower L) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-lossExp)))
    (hselected : selected.Nonempty)
    (hcount : (selected.card : ENNReal) ≤
      K * (((delta : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))))
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta)
    (habsorb :
      4 *
          (contractedJohnMiddleActualFixedCoefficient
              K frostmanEpsilon frostmanBeta gamma lossExp *
            (((delta : ENNReal) / (rho : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma lossExp kappa)) ≤
        (globalDelta : ENNReal) ^ (10 * globalEta)) :
    4 * (stickyFiberSourceShading S Y q.1).averageMultiplicity ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          delta rho selected.card gamma := by
  let sourceC := selectedFiberLowCFSourceConstant S q selected lower L
  let sourceLoss := stickyFiberContractedJohnSourceClosedLoss
    (selectedFiberLowCFCardEnvelope S q selected lower L)
  let proxyD := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne q
  have hsourceKT : IsKatzTao sourceC
      (activeSubtypeFamily (S.fiberFamily q.1) selected) := by
    simpa only [sourceC, selectedFiberLowCFSourceConstant] using
      (selectedFiber_isKatzTao_of_isFrostmanIn
        S hrho q selected hLow)
  have hnormalizedKT : IsKatzTao
      (128 * stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne q sourceC)
      (restrictActualTubeDatum
        (eighthNormalizedDatum proxyD) selected).family.bodyFamily := by
    simpa only [proxyD] using
      (selectedFiberContractedJohn_restrictEighthNormalized_isKatzTao
        S Y hrho hrhoOne hdelta hdeltaHalf hdeltaRho q selected hsourceKT)
  have hcardEnvelopeTop :
      selectedFiberLowCFCardEnvelope S q selected lower L ≠ ∞ := by
    unfold selectedFiberLowCFCardEnvelope
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hlowerTop
        (ENNReal.mul_ne_top (by norm_num) hLTop))
      (by simp)
  have hloss0 : sourceLoss ≠ 0 := by
    dsimp only [sourceLoss]
    unfold stickyFiberContractedJohnSourceClosedLoss
    positivity
  have hlossTop : sourceLoss ≠ ∞ := by
    dsimp only [sourceLoss]
    unfold stickyFiberContractedJohnSourceClosedLoss
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top (by norm_num) hcardEnvelopeTop)), by norm_num⟩
  have hproxyEighth : 0 < contractedJohnProxyRadius delta rho / 8 :=
    div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hproxyHalf : contractedJohnProxyRadius delta rho ≤ (2 : NNReal)⁻¹ :=
    stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho
  have hproxyEighthHalf :
      contractedJohnProxyRadius delta rho / 8 ≤ (2 : NNReal)⁻¹ := by
    calc
      contractedJohnProxyRadius delta rho / 8 ≤
          (2 : NNReal)⁻¹ / 8 := by gcongr
      _ ≤ (2 : NNReal)⁻¹ := by
        rw [← NNReal.coe_le_coe]
        norm_num
  have hscaleEq :
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal)) =
        (3 / 64 : ENNReal) *
          ((delta : ENNReal) / (rho : ENNReal)) :=
    coe_contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
      (delta := delta) hrho
  have hstrict :=
    four_mul_sourceAverage_le_globalPower_mul_sectionEight
      (globalDelta := globalDelta) (fineScale := delta) (coarseScale := rho)
      hF proxyD selected sourceLoss
        (128 * stickyFiberContractedJohnProxyKatzTaoConstant
          S hrho hrhoOne q sourceC) K
      hloss0 hlossTop hdelta0 hadmissible
      (by simpa only [sourceLoss] using hcard)
      (by simpa only [sourceLoss, proxyD] using hmass)
      hnormalizedKT
      (by simpa only [sourceLoss, proxyD] using hdensityBudget)
      (by simpa only [sourceLoss, sourceC, proxyD] using hbaseBudget)
      hdelta hrho hproxyEighth hproxyEighthHalf hbetaTwo hgammaTwo hgap
      hscaleEq (by simpa only [sourceLoss] using hlossPower) hselected hcount
      habsorb
  have hproxyAverage :
      proxyD.shading.averageMultiplicity =
        (stickyFiberSourceShading S Y q.1).averageMultiplicity := by
    dsimp only [proxyD]
    exact stickyFiberContractedJohnProxyShading_averageMultiplicity
      S Y hrho hrhoOne q
  rw [← hproxyAverage]
  exact hstrict

#print axioms four_mul_selectedFiberSourceAverage_le_strictMiddle

end
end Family8StickySelectedFiberLowCFStrictMiddleV2
