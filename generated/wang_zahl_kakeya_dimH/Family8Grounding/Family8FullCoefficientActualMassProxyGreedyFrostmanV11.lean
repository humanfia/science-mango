import Family8Grounding.Family8FullCoefficientActualMassProxyDatumV11
import Family8Grounding.Family8FullCoefficientActualMassProxyFrostmanV9
import Family8Grounding.Family8ActualDatumCardRetentionFrostmanV2
import Family8Grounding.Family8ActualDatumCardDensityFrostmanHypothesesV1

/-!
# Automatic greedy Frostman handoff for the ten-radius full-metric proxy, V10

The proxy first inherits the exact critical-ball card-quotient Frostman
constant.  Direct greedy selection then supplies admissibility and the
literal card/density/average retention fields.  Exactly two scalar budgets
remain to obtain the paper-level `FrostmanHypotheses` on the selected datum.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
set_option linter.unusedVariables false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullCoefficientActualMassProxyGreedyFrostmanV11

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family8ActualDatumCardDensityFrostmanHypothesesV1
open Family8ActualDatumCardRetentionFrostmanV2
open Family8ActualRestrictedMassWeightedCriticalBallShadingV4
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7CriticalScaleProxyVolumeLossV2
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8FullCoefficientActualMassProxyDatumV11
open Family8FullCoefficientActualMassProxyFrostmanV9
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalBallExactCardFrostmanV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyDatumV4
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

/-- Full proxy Frostman coefficient before direct greedy restriction. -/
def fullCoefficientActualMassProxyFrostmanLoss
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (X : Set Space) (C : ENNReal) : ENNReal :=
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  criticalScaleAffineProxyVolumeLoss *
    (affineJacobian
        (weightedCanonicalCriticalScaleAffineEquiv S W).symm *
      (C * (16 * weightedCanonicalCriticalBallCardLoss W)))

/-- The selected exact proxy datum inherits the source proxy Frostman
certificate with the direct-greedy cardinality loss. -/
theorem fullCoefficientProxyGreedyOutput_selected_isFrostmanIn
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (X : Set Space) (hX : MeasurableSet X)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal}
    (hF : IsFrostmanOn C S.family.bodyFamily active unitBallBody)
    (haxis : ∀ i : FullCoefficientActualMassProxyIndex S Y active hactive
      hradius htenRadiusSixteen X,
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S
          (fullCoefficientActualMassNormData S active hactive
            hradius htenRadiusSixteen Y X))
        (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S
            (fullCoefficientActualMassNormData S active hactive
              hradius htenRadiusSixteen Y X)) * (radius : Real) ≤
        (criticalScaleProxyRadius radius
          (fullCoefficientActualMassNormData S active hactive
            hradius htenRadiusSixteen Y X).criticalScale
          (weightedCanonicalCriticalScale_pos
            (fullCoefficientActualMassNormData S active hactive
              hradius htenRadiusSixteen Y X)) : Real))
    (O : let W := fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y X
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen X hX haxis htransverse
      FullCoefficientActualMassProxyGreedyOutput A (W.family.card + 1)) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    let A := fullCoefficientActualMassProxyDatum S Y active hactive
      hradius htenRadiusSixteen X hX haxis htransverse
    IsFrostmanIn
      (fullCoefficientActualMassProxyFrostmanLoss S Y active hactive
          hradius htenRadiusSixteen X C * (16 * (W.family.card + 1 : Nat)))
      (restrictActualTubeDatum A O.selected).family.bodyFamily
      unitBallBody := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  let A := fullCoefficientActualMassProxyDatum S Y active hactive
    hradius htenRadiusSixteen X hX haxis htransverse
  let proxyLoss := fullCoefficientActualMassProxyFrostmanLoss
    S Y active hactive hradius htenRadiusSixteen X C
  have hproxy : IsFrostmanIn proxyLoss A.family.bodyFamily unitBallBody := by
    simpa only [A, proxyLoss, fullCoefficientActualMassProxyFrostmanLoss,
      fullCoefficientActualMassProxyDatum,
      weightedCanonicalCriticalScaleProxyDatum, W] using
        fullCoefficientActualMass_proxyFamily_isFrostmanIn
          S active hactive hradius hradiusHalf htenRadiusSixteen Y X
            hactiveSource hcontained hF
  exact restrictActualTubeDatum_isFrostmanIn_of_card_retention
    A O.selected unitBallBody hproxy O.radius_le_half O.card_retention

/-- The exact retained density and constant comparisons turn the selected
proxy into the paper-level Frostman input. -/
theorem fullCoefficientProxyGreedyOutput_selected_frostmanHypotheses
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (X : Set Space) (hX : MeasurableSet X)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal}
    (hF : IsFrostmanOn C S.family.bodyFamily active unitBallBody)
    (haxis : ∀ i : FullCoefficientActualMassProxyIndex S Y active hactive
      hradius htenRadiusSixteen X,
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S
          (fullCoefficientActualMassNormData S active hactive
            hradius htenRadiusSixteen Y X))
        (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S
            (fullCoefficientActualMassNormData S active hactive
              hradius htenRadiusSixteen Y X)) * (radius : Real) ≤
        (criticalScaleProxyRadius radius
          (fullCoefficientActualMassNormData S active hactive
            hradius htenRadiusSixteen Y X).criticalScale
          (weightedCanonicalCriticalScale_pos
            (fullCoefficientActualMassNormData S active hactive
              hradius htenRadiusSixteen Y X)) : Real))
    (O : let W := fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y X
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen X hX haxis htransverse
      FullCoefficientActualMassProxyGreedyOutput A (W.family.card + 1))
    {eta : Real}
    (hdensityBudget :
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen X hX haxis htransverse
      (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ eta ≤
        A.shading.shadingDensity / (W.family.card + 1 : Nat))
    (hconstantBudget :
      let W := fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X
      fullCoefficientActualMassProxyFrostmanLoss S Y active hactive
          hradius htenRadiusSixteen X C * (16 * (W.family.card + 1 : Nat)) ≤
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : ENNReal) ^ (-eta)) :
    let A := fullCoefficientActualMassProxyDatum S Y active hactive
      hradius htenRadiusSixteen X hX haxis htransverse
    FrostmanHypotheses (restrictActualTubeDatum A O.selected) eta := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  let A := fullCoefficientActualMassProxyDatum S Y active hactive
    hradius htenRadiusSixteen X hX haxis htransverse
  let proxyLoss := fullCoefficientActualMassProxyFrostmanLoss
    S Y active hactive hradius htenRadiusSixteen X C
  have hproxy : IsFrostmanIn proxyLoss A.family.bodyFamily unitBallBody := by
    simpa only [A, proxyLoss, fullCoefficientActualMassProxyFrostmanLoss,
      fullCoefficientActualMassProxyDatum,
      weightedCanonicalCriticalScaleProxyDatum, W] using
        fullCoefficientActualMass_proxyFamily_isFrostmanIn
          S active hactive hradius hradiusHalf htenRadiusSixteen Y X
            hactiveSource hcontained hF
  exact restrictActualTubeDatum_frostmanHypotheses_of_card_density_retention
    A O.selected hproxy O.radius_le_half O.card_retention
      hdensityBudget O.density_retention hconstantBudget

#print axioms fullCoefficientActualMassProxyFrostmanLoss
#print axioms fullCoefficientProxyGreedyOutput_selected_isFrostmanIn
#print axioms fullCoefficientProxyGreedyOutput_selected_frostmanHypotheses

end
end Family8FullCoefficientActualMassProxyGreedyFrostmanV11
