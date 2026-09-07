import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyGreedyV2
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyChartV1
import Family8Grounding.Family8Family7GenericNativeHighActivePatternProxyInputV1
import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxyGeometryV1
import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxySupportV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8Family7GenericNativeHighActivePatternWeightedCanonicalGreedyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7GenericNativeHighActivePatternProxyInputV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyGeometryV1
open Family8Family7GenericNativeHighArbitraryWeightedProxySupportV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyDatumV4
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open Family8WeightedCanonicalCriticalScaleProxyGreedyV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

/-- The active-pattern occurrence datum instantiates the rebuilt weighted
canonical proxy on the same critical ball.  A genuine `1/5` radius cap gives
the charted, unit-supported admissible greedy restriction and all four
quantitative retention inequalities, without a conclusion-valued callback. -/
theorem exists_activePattern_weightedCanonicalProxy_greedy_of_radius
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily)
    (hcontained : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hproxyRadius :
      criticalScaleProxyRadius radius
          (genericNativeHighActivePatternWeightedNormData D G c).criticalScale
          (weightedCanonicalCriticalScale_pos
            (genericNativeHighActivePatternWeightedNormData D G c)) ≤
        (1 / 5 : NNReal)) :
    let W := genericNativeHighActivePatternWeightedNormData D G c
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
      (∀ i : {i // i ∈ W.criticalBall},
        (1 / 2 : Real) ≤
          |((weightedCanonicalCriticalScaleProxyFamily S W).tubes i).axis.direction 2|) ∧
      let A := weightedCanonicalCriticalScaleProxyDatum
        S W Y haxis htransverse
      ∃ selected : Finset {i // i ∈ W.criticalBall},
        selected.Nonempty ∧
        (restrictActualTubeDatum A selected).IsAdmissible ∧
        (Fintype.card {i // i ∈ W.criticalBall} : ENNReal) ≤
          (W.family.card + 1 : Nat) * (selected.card : ENNReal) ∧
        A.shading.shadingMass ≤
          (W.family.card + 1 : Nat) *
            (restrictActualTubeDatum A selected).shading.shadingMass ∧
        A.shading.shadingDensity / (W.family.card + 1 : Nat) ≤
          (restrictActualTubeDatum A selected).shading.shadingDensity ∧
        A.shading.averageMultiplicity ≤
          (W.family.card + 1 : Nat) *
            (restrictActualTubeDatum A selected).shading.averageMultiplicity := by
  classical
  let W := genericNativeHighActivePatternWeightedNormData D G c
  let P := genericNativeHighActivePatternProxyInput D G c
  have H := genericNativeHighArbitraryWeightedCriticalScaleProxyGeometry
    D P hambientSource
  have haxis : ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1 := by
    change ∀ i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P,
      ‖affineImageAxisVector
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
        (S.family.tubes i.1)‖ ≤ 1
    exact H.axisLength
  have htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            (radius : Real) ≤
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real) := by
    change affineLinearOperatorNorm
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
          (radius : Real) ≤
      (criticalScaleProxyRadius radius
        (genericNativeHighWeightedNormData D P.center P.weight).criticalScale
        (genericNativeHighArbitraryWeightedCriticalScale_pos D P) : Real)
    exact H.transverseRadius
  have hchart : ∀ i : {i // i ∈ W.criticalBall},
      (1 / 2 : Real) ≤
        |((weightedCanonicalCriticalScaleProxyFamily S W).tubes i).axis.direction 2| := by
    change ∀ i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P,
      (1 / 2 : Real) ≤
        |((genericNativeHighArbitraryWeightedCriticalScaleProxyFamily
          D P).tubes i).axis.direction 2|
    exact H.chart
  have hproxyRadiusW :
      criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) ≤
        (1 / 5 : NNReal) := by
    exact hproxyRadius
  have hdeltaHalf :
      criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) ≤
        (2 : NNReal)⁻¹ :=
    hproxyRadiusW.trans (by
      exact_mod_cast
        (show (1 / 5 : Real) ≤ (2 : Real)⁻¹ by norm_num))
  have hsupportGeneric :=
    genericNativeHighArbitraryWeightedProxyFamily_contained_in_unit_ball
      D P hambientSource hcontained (by
        change criticalScaleProxyRadius radius W.criticalScale
            (weightedCanonicalCriticalScale_pos W) ≤
          (1 / 5 : NNReal)
        exact hproxyRadiusW)
  have hsupport : ∀ i : {i // i ∈ W.criticalBall},
      ((weightedCanonicalCriticalScaleProxyFamily S W).tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
    intro i
    change ((genericNativeHighArbitraryWeightedCriticalScaleProxyFamily
      D P).tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1
    exact hsupportGeneric i
  refine ⟨haxis, htransverse, hchart, ?_⟩
  exact exists_weightedCanonicalCriticalScaleProxy_greedyAdmissible
    S W Y D.hradius haxis htransverse hdeltaHalf hsupport

end

end Family8Family7GenericNativeHighActivePatternWeightedCanonicalGreedyV2
