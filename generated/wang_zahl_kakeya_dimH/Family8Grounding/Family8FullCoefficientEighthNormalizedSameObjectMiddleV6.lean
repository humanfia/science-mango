import Family8Grounding.Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
import Family8Grounding.Family8FullCoefficientEighthNormalizedStrictMiddleV9

/-!
# Same-object whole-window middle estimate

This adapter specializes the full-coefficient strict-middle theorem to the
whole spatial window.  A caller supplies an exact equality between that
active restricted average and its literal Family7 graph average; no family,
graph, or greedy selection is changed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option linter.unusedVariables false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullCoefficientEighthNormalizedSameObjectMiddleV6

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
open Family8FullCoefficientEighthNormalizedStrictMiddleV9
open Family8FullCoefficientCriticalScaleEighthRelativeFixedV3
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-- The strict middle estimate, rewritten to any literal average identified
with the exact active whole-window source. -/
theorem outerLoss_mul_sameObjectAverage_le_strictMiddle
    {fine coarse globalDelta delta0 : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource (fine / 8) iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (sourceAverage : ENNReal)
    (hsourceAverage :
      (activeRestrictedShading S Y active Set.univ
        MeasurableSet.univ).averageMultiplicity = sourceAverage)
    (hradius : 0 < fine / 8)
    (hradiusHalf : fine / 8 ≤ (2 : NNReal)⁻¹)
    (htenRadiusSixteen : 10 * ((fine / 8 : NNReal) : Real) ≤ 16)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal}
    (hFsource : IsFrostmanOn C S.family.bodyFamily active unitBallBody)
    (haxis :
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y Set.univ;
      ∀ i : {i // i ∈ W.criticalBall},
        ‖affineImageAxisVector
          (weightedCanonicalCriticalScaleAffineEquiv S W)
          (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y Set.univ
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            ((fine / 8 : NNReal) : Real) ≤
        (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real))
    (O :
      let W := fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y Set.univ
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen Set.univ MeasurableSet.univ
          haxis htransverse
      FullCoefficientActualMassProxyGreedyOutput A (W.family.card + 1))
    {frostmanBeta frostmanEpsilon frostmanEta gamma lossExp kappa
      globalEta : Real}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon frostmanEta delta0)
    (hdensityBudget :
      let W := fullCoefficientActualMassNormData
          S active hactive hradius htenRadiusSixteen Y Set.univ
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen Set.univ MeasurableSet.univ
          haxis htransverse
      (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ frostmanEta ≤
        A.shading.shadingDensity / (W.family.card + 1 : Nat))
    (hconstantBudget :
      let W := fullCoefficientActualMassNormData
          S active hactive hradius htenRadiusSixteen Y Set.univ
      fullCoefficientActualMassProxyFrostmanLoss S Y active hactive
          hradius htenRadiusSixteen Set.univ C *
            (16 * (W.family.card + 1 : Nat)) ≤
        (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^
            (-frostmanEta))
    (hdelta0 :
      let W := fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y Set.univ
      criticalScaleProxyRadius (fine / 8) W.criticalScale
        (weightedCanonicalCriticalScale_pos W) ≤ delta0)
    (hfine : 0 < fine) (hcoarse : 0 < coarse)
    (hbetaTwo : frostmanBeta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - frostmanBeta)
    {K outerLoss : ENNReal}
    (hlossPower :
      let W := fullCoefficientActualMassNormData
          S active hactive hradius htenRadiusSixteen Y Set.univ
      (W.family.card + 1 : Nat) ≤
        (criticalScaleProxyRadius (fine / 8) W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ (-lossExp))
    (hcount :
      let W := fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y Set.univ
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen Set.univ MeasurableSet.univ
          haxis htransverse
      (O.selected.card : ENNReal) ≤
        K * (((fine : ENNReal) / (coarse : ENNReal)) ^ (-(2 + kappa))))
    (habsorb :
      let W := fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y Set.univ
      outerLoss *
          (arbitraryFixedMiddleActualCoefficient
              (fullCoefficientEighthRelativeFixed coarse W) K
              frostmanEpsilon frostmanBeta gamma lossExp *
            (((fine : ENNReal) / (coarse : ENNReal)) ^
              contractedJohnMiddleRatioGain
                frostmanEpsilon frostmanBeta gamma lossExp kappa)) ≤
        (globalDelta : ENNReal) ^ (10 * globalEta)) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y Set.univ
    outerLoss * sourceAverage ≤
      (globalDelta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          fine coarse O.selected.card gamma := by
  dsimp only at haxis htransverse O hdensityBudget hconstantBudget hdelta0
  dsimp only at hlossPower hcount habsorb ⊢
  let f0 : Real → Real := fun _x => 0
  have hf0 : Measurable f0 := measurable_const
  have hstrict :=
    outerLoss_mul_activeRestrictedAverage_le_strictMiddle
      (coarse := coarse) (globalDelta := globalDelta) (delta0 := delta0)
      (frostmanBeta := frostmanBeta)
      (frostmanEpsilon := frostmanEpsilon)
      (frostmanEta := frostmanEta) (gamma := gamma)
      (lossExp := lossExp) (kappa := kappa) (globalEta := globalEta)
      (K := K) (outerLoss := outerLoss)
      S Y active hactive f0 hf0 Set.univ MeasurableSet.univ
      hradius hradiusHalf htenRadiusSixteen hactiveSource hcontained
      hFsource
  simp only [Set.preimage_univ] at hstrict
  have hraw :=
    hstrict haxis htransverse O hF
      hdensityBudget hconstantBudget hdelta0
      hfine hcoarse hbetaTwo hgammaTwo hgap
      hlossPower hcount habsorb
  rw [← hsourceAverage]
  exact hraw

#print axioms
  outerLoss_mul_sameObjectAverage_le_strictMiddle

end
end Family8FullCoefficientEighthNormalizedSameObjectMiddleV6
