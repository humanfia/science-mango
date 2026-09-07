import Family8Grounding.Family8FullCoefficientActualMassProxyAverageV10
import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1
import Family8Grounding.Family8FullCoefficientActualMassProxySupportV10
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyDatumV4
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyGreedyV2

/-!
# Actual datum and automatic direct greedy refinement for the ten-radius full-metric proxy, V11

This packages the exact restricted-mass proxy shading constructed by the
full-coefficient critical ball.  In the large-scale branch the proxy has
unit-ball support and radius at most one half, so the generic direct greedy
theorem produces an admissible same-object restriction.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullCoefficientActualMassProxyDatumV11

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ActualRestrictedMassWeightedCriticalBallShadingV4
open Family8ContractedJohnActualTubeProxyV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8FullCoefficientActualMassProxyGeometryV7
open Family8FullCoefficientActualMassProxySupportV10
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyDatumV4
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open Family8WeightedCanonicalCriticalScaleProxyGreedyV2
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

abbrev FullCoefficientActualMassProxyIndex
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (X : Set Space) :=
  {i // i ∈ (fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X).criticalBall}

/-- The literal proxy datum on the same actual-mass critical ball. -/
def fullCoefficientActualMassProxyDatum
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (X : Set Space) (hX : MeasurableSet X)
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
              hradius htenRadiusSixteen Y X)) : Real)) :
    ActualTubeDatum
      (criticalScaleProxyRadius radius
        (fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y X).criticalScale
        (weightedCanonicalCriticalScale_pos
          (fullCoefficientActualMassNormData S active hactive
            hradius htenRadiusSixteen Y X)))
      (FullCoefficientActualMassProxyIndex S Y active hactive
        hradius htenRadiusSixteen X) :=
  weightedCanonicalCriticalScaleProxyDatum S
    (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X)
    (restrictedShading Y X hX) haxis htransverse

/-- Quantitative output of direct greedy selection on the exact proxy. -/
structure FullCoefficientActualMassProxyGreedyOutput
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (A : ActualTubeDatum delta index) (loss : Nat) where
  radius_le_half : delta ≤ (2 : NNReal)⁻¹
  selected : Finset index
  selected_nonempty : selected.Nonempty
  admissible : (restrictActualTubeDatum A selected).IsAdmissible
  card_retention : (Fintype.card index : ENNReal) ≤
    (loss : ENNReal) * (selected.card : ENNReal)
  mass_retention : A.shading.shadingMass ≤
    (loss : ENNReal) *
      (restrictActualTubeDatum A selected).shading.shadingMass
  density_retention : A.shading.shadingDensity / (loss : ENNReal) ≤
    (restrictActualTubeDatum A selected).shading.shadingDensity
  average_retention : A.shading.averageMultiplicity ≤
    (loss : ENNReal) *
      (restrictActualTubeDatum A selected).shading.averageMultiplicity

/-- In the tenfold-separated branch, construct the actual proxy datum and
its admissible greedy restriction. -/
theorem exists_fullCoefficientActualMassProxyGreedyOutput
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (X : Set Space) (hX : MeasurableSet X)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    ∃ (haxis : ∀ i : {i // i ∈ W.criticalBall},
        ‖affineImageAxisVector
          (weightedCanonicalCriticalScaleAffineEquiv S W)
          (S.family.tubes i.1)‖ ≤ 1)
      (htransverse :
        affineLinearOperatorNorm
            (weightedCanonicalCriticalScaleAffineEquiv S W) *
              (radius : Real) ≤
          (criticalScaleProxyRadius radius W.criticalScale
            (weightedCanonicalCriticalScale_pos W) : Real)),
      let A := fullCoefficientActualMassProxyDatum S Y active hactive
        hradius htenRadiusSixteen X hX haxis htransverse
      Nonempty (FullCoefficientActualMassProxyGreedyOutput A
        (W.family.card + 1)) := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  obtain ⟨haxis, htransverse, _hchart⟩ :=
    exists_fullCoefficientActualMass_proxyGeometry
      S active hactive hradius htenRadiusSixteen Y X hactiveSource
  obtain ⟨_hproxyFifth, hproxyHalf, hsupport⟩ :=
    fullCoefficientActualMass_proxySupport
      S active hactive hradius htenRadiusSixteen Y X hactiveSource
        hcontained
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hdensity, havg⟩ :=
    exists_weightedCanonicalCriticalScaleProxy_greedyAdmissible
      S W (restrictedShading Y X hX) hradius haxis htransverse
        hproxyHalf hsupport
  exact ⟨haxis, htransverse, ⟨{
    radius_le_half := hproxyHalf
    selected := selected
    selected_nonempty := hselected
    admissible := hadmissible
    card_retention := hcard
    mass_retention := hmass
    density_retention := hdensity
    average_retention := havg
  }⟩⟩

#print axioms fullCoefficientActualMassProxyDatum
#print axioms FullCoefficientActualMassProxyGreedyOutput
#print axioms exists_fullCoefficientActualMassProxyGreedyOutput

end
end Family8FullCoefficientActualMassProxyDatumV11
