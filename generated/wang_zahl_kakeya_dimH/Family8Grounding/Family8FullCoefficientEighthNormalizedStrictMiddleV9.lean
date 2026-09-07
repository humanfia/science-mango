import Family8Grounding.Family8ActualRestrictedMassWeightedCriticalBallShadingV4
import Family8Grounding.Family8ArbitraryFixedRelativeScaleActualVolumeEnvelopeV1
import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Family8Grounding.Family8FullCoefficientActualMassProxyAverageV10
import Family8Grounding.Family8FullCoefficientActualMassProxyGreedyFrostmanV11
import Family8Grounding.Family8FullCoefficientCriticalScaleEighthRelativeFixedV3
import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import Mathlib.Tactic

/-!
# Strict middle estimate from the eighth-normalized full-coefficient proxy, V2

The proxy source lives at radius `fine / 8`, but the Section-8 factor remains
at the original physical scales `fine -> coarse`.  The exact relative fixed
coefficient is therefore `coarse / (4 * criticalScale)`.  This theorem keeps
one literal weighted critical ball, one literal direct-greedy selection, and
one selected actual datum from average retention through the Frostman
endpoint and the final Section-8 envelope.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullCoefficientEighthNormalizedStrictMiddleV9

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8ActualRestrictedMassWeightedCriticalBallShadingV4
open Family8ArbitraryFixedRelativeScaleActualVolumeEnvelopeV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8FullCoefficientActualMassProxyAverageV10
open Family8FullCoefficientActualMassProxyDatumV11
open Family8FullCoefficientActualMassProxyGreedyFrostmanV11
open Family8FullCoefficientCriticalScaleEighthRelativeFixedV3
open Family8FullCoefficientCriticalScaleRatioV2
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyAverageV2
open Family8WeightedCanonicalCriticalScaleProxyShadingV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-- The exact full-metric proxy, its direct-greedy loss, the selected
Frostman endpoint, and the arbitrary-fixed envelope imply the strict
Section-8 middle estimate at the original physical scales. -/
theorem outerLoss_mul_activeRestrictedAverage_le_strictMiddle
    {fine coarse globalDelta delta0 : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource (fine / 8) iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (f : Real → Real) (hf : Measurable f)
    (E : Set (Real × Real)) (hE : MeasurableSet E)
    (hradius : 0 < fine / 8)
    (hradiusHalf : fine / 8 ≤ (2 : NNReal)⁻¹)
    (htenRadiusSixteen : 10 * ((fine / 8 : NNReal) : Real) ≤ 16)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal}
    (hFsource : IsFrostmanOn C S.family.bodyFamily active unitBallBody)
    (haxis : let X := twistedProjection f ⁻¹' E
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      ∀ i : {i // i ∈ W.criticalBall},
        ‖affineImageAxisVector
          (weightedCanonicalCriticalScaleAffineEquiv S W)
          (S.family.tubes i.1)‖ ≤ 1)
    (htransverse : let X := twistedProjection f ⁻¹' E
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            ((fine / 8 : NNReal) : Real) ≤
        (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real))
    (O : let X := twistedProjection f ⁻¹' E
      let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen X hX haxis htransverse
      FullCoefficientActualMassProxyGreedyOutput A (W.family.card + 1))
    {frostmanBeta frostmanEpsilon frostmanEta gamma lossExp kappa
      globalEta : Real}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (hdensityBudget : let X := twistedProjection f ⁻¹' E
      let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen X hX haxis htransverse
      (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ frostmanEta ≤
        A.shading.shadingDensity / (W.family.card + 1 : Nat))
    (hconstantBudget : let X := twistedProjection f ⁻¹' E
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      fullCoefficientActualMassProxyFrostmanLoss S Y active hactive
          hradius htenRadiusSixteen X C * (16 * (W.family.card + 1 : Nat)) ≤
        (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^
            (-frostmanEta))
    (hdelta0 : let X := twistedProjection f ⁻¹' E
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      criticalScaleProxyRadius (fine / 8) W.criticalScale
        (weightedCanonicalCriticalScale_pos W) ≤ delta0)
    (hfine : 0 < fine) (hcoarse : 0 < coarse)
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta)
    {K outerLoss : ENNReal}
    (hlossPower : let X := twistedProjection f ⁻¹' E
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      (W.family.card + 1 : Nat) ≤
        (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ (-lossExp))
    (hcount : (O.selected.card : ENNReal) ≤
        K * (((fine : ENNReal) / (coarse : ENNReal)) ^ (-(2 + kappa))))
    (habsorb : let X := twistedProjection f ⁻¹' E
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      outerLoss *
          (arbitraryFixedMiddleActualCoefficient
              (fullCoefficientEighthRelativeFixed coarse W) K
              frostmanEpsilon frostmanBeta gamma lossExp *
            (((fine : ENNReal) / (coarse : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma lossExp kappa)) ≤
        (globalDelta : ENNReal) ^ (10 * globalEta)) :
    let X := twistedProjection f ⁻¹' E
    let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
    outerLoss *
        (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          fine coarse O.selected.card gamma := by
  dsimp only at haxis htransverse O hdensityBudget hconstantBudget hdelta0
  dsimp only at hlossPower hcount habsorb ⊢
  let X := twistedProjection f ⁻¹' E
  let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  let A := fullCoefficientActualMassProxyDatum S Y active hactive
    hradius htenRadiusSixteen X hX haxis htransverse
  let R := restrictActualTubeDatum A O.selected
  let loss : ENNReal := (W.family.card + 1 : Nat)
  have hcritical :=
    activeRestricted_averageMultiplicity_le_fullCoefficientCriticalBall
      S Y active hactive f hf E hE hradius htenRadiusSixteen
        hactiveSource hcontained
  have hproxyEq :=
    weightedCanonicalCriticalScaleProxyShading_averageMultiplicity
      S W (restrictedShading Y X hX) haxis htransverse
  have hsourceProxy :
      (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
        A.shading.averageMultiplicity := by
    calc
      (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
          (weightedCanonicalCriticalBallShading S W
            (restrictedShading Y X hX)).averageMultiplicity := by
        simpa only [X, hX, W] using hcritical
      _ = (weightedCanonicalCriticalScaleProxyShading S W
            (restrictedShading Y X hX) haxis htransverse).averageMultiplicity := hproxyEq.symm
      _ = A.shading.averageMultiplicity := rfl
  have hselectedFrostman : FrostmanHypotheses R frostmanEta := by
    simpa only [R, A, W, X, hX] using
      (fullCoefficientProxyGreedyOutput_selected_frostmanHypotheses
        S Y active hactive hradius hradiusHalf htenRadiusSixteen X hX
          hactiveSource hcontained hFsource haxis htransverse O
            hdensityBudget hconstantBudget)
  have hendpoint : R.shading.averageMultiplicity ≤
      frostmanMultiplicityRHS
        (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W))
        R.actualFamilyVolume frostmanEpsilon frostmanBeta := by
    exact FrostmanAtParameters.apply hF R O.admissible hdelta0
      hselectedFrostman
  have hsourceRHS :
      (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
        loss * frostmanMultiplicityRHS
          (criticalScaleProxyRadius (fine / 8) W.criticalScale
            (weightedCanonicalCriticalScale_pos W))
          R.actualFamilyVolume frostmanEpsilon frostmanBeta := by
    calc
      (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
          A.shading.averageMultiplicity := hsourceProxy
      _ ≤ loss * R.shading.averageMultiplicity := by
        simpa only [loss, R] using O.average_retention
      _ ≤ loss * frostmanMultiplicityRHS
          (criticalScaleProxyRadius (fine / 8) W.criticalScale
            (weightedCanonicalCriticalScale_pos W))
          R.actualFamilyVolume frostmanEpsilon frostmanBeta :=
        mul_le_mul' le_rfl hendpoint
  have hproxyPos : 0 < criticalScaleProxyRadius (fine / 8)
      W.criticalScale (weightedCanonicalCriticalScale_pos W) := by
    rw [criticalScaleProxyRadius_eq_two_mul_ratio]
    exact mul_pos (by norm_num)
      (div_pos hradius (weightedCanonicalCriticalScaleNNReal_pos W))
  have hcountPos : 0 < Fintype.card {i // i ∈ O.selected} := by
    simpa only [Fintype.card_coe] using O.selected_nonempty.card_pos
  have hcountSubtype :
      (Fintype.card {i // i ∈ O.selected} : ENNReal) ≤
        K * (((fine : ENNReal) / (coarse : ENNReal)) ^
          (-(2 + kappa))) := by
    simpa only [Fintype.card_coe] using hcount
  have hrelative :
      loss * frostmanMultiplicityRHS
          (criticalScaleProxyRadius (fine / 8) W.criticalScale
            (weightedCanonicalCriticalScale_pos W))
          R.actualFamilyVolume frostmanEpsilon frostmanBeta ≤
        arbitraryFixedMiddleActualCoefficient
            (fullCoefficientEighthRelativeFixed coarse W) K
            frostmanEpsilon frostmanBeta gamma lossExp *
          (((fine : ENNReal) / (coarse : ENNReal)) ^
            contractedJohnMiddleRatioGain
              frostmanEpsilon frostmanBeta gamma lossExp kappa) *
          sectionEightScaleCountFrostmanFactor
            fine coarse O.selected.card gamma := by
    simpa only [R, Fintype.card_coe] using
      (loss_mul_actualRHS_le_arbitraryFixed_mul_ratioGain_mul_sectionEight
        (D := R) (loss := loss)
        (fixed := fullCoefficientEighthRelativeFixed coarse W) (K := K)
        (epsilon := frostmanEpsilon) (beta := frostmanBeta)
        (gamma := gamma) (lossExp := lossExp) (kappa := kappa)
        hfine hcoarse hproxyPos O.radius_le_half hbetaTwo hgammaTwo hgap
        (fullCoefficientEighthRelativeFixed_ne_top hcoarse W)
        (coe_eighth_criticalScaleProxyRadius_eq_relativeFixed_mul_ratio
          fine coarse hcoarse W)
        hlossPower hcountPos hcountSubtype)
  calc
    outerLoss *
        (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
      outerLoss *
        (loss * frostmanMultiplicityRHS
          (criticalScaleProxyRadius (fine / 8) W.criticalScale
            (weightedCanonicalCriticalScale_pos W))
          R.actualFamilyVolume frostmanEpsilon frostmanBeta) :=
      mul_le_mul' le_rfl hsourceRHS
    _ ≤ outerLoss *
        (arbitraryFixedMiddleActualCoefficient
            (fullCoefficientEighthRelativeFixed coarse W) K
            frostmanEpsilon frostmanBeta gamma lossExp *
          (((fine : ENNReal) / (coarse : ENNReal)) ^
            contractedJohnMiddleRatioGain
              frostmanEpsilon frostmanBeta gamma lossExp kappa) *
          sectionEightScaleCountFrostmanFactor
            fine coarse O.selected.card gamma) :=
      mul_le_mul' le_rfl hrelative
    _ = (outerLoss *
          (arbitraryFixedMiddleActualCoefficient
              (fullCoefficientEighthRelativeFixed coarse W) K
              frostmanEpsilon frostmanBeta gamma lossExp *
            (((fine : ENNReal) / (coarse : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma lossExp kappa))) *
        sectionEightScaleCountFrostmanFactor
          fine coarse O.selected.card gamma := by
      ac_rfl
    _ ≤ (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          fine coarse O.selected.card gamma :=
      mul_le_mul' habsorb le_rfl

#print axioms outerLoss_mul_activeRestrictedAverage_le_strictMiddle

end
end Family8FullCoefficientEighthNormalizedStrictMiddleV9
