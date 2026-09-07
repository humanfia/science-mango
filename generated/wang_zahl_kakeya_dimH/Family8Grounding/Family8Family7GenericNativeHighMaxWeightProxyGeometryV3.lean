import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyAxisLengthV1
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyTransverseRadiusV2
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyChartV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighMaxWeightProxyGeometryV3

open LeanEval.Analysis.WangZahlKakeya
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
open Family8Family7GenericNativeHighActivePatternMaxWeightFiberSubsetV1
open Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyAxisLengthV1
open Family8WeightedCanonicalCriticalScaleProxyChartV1
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open Family8WeightedCanonicalCriticalScaleProxyTransverseRadiusV2
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! The restricted maximal-occurrence-weight datum inherits the literal
critical-scale proxy geometry from the same physical ambient. -/

theorem exists_genericNativeHighActivePatternMaxWeight_proxyGeometry
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0)
    (hambientSource : physical.ambient ⊆ S.source) :
    let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
    ∃ (_haxis : ∀ i : {i // i ∈ W.criticalBall},
        ‖affineImageAxisVector
          (weightedCanonicalCriticalScaleAffineEquiv S W)
          (S.family.tubes i.1)‖ ≤ 1)
      (_htransverse :
        affineLinearOperatorNorm
            (weightedCanonicalCriticalScaleAffineEquiv S W) *
              (radius : Real) ≤
          (criticalScaleProxyRadius radius W.criticalScale
            (weightedCanonicalCriticalScale_pos W) : Real)),
      ∀ i : {i // i ∈ W.criticalBall},
        (1 / 2 : Real) ≤
          |((weightedCanonicalCriticalScaleProxyFamily S W).tubes i).axis.direction 2| := by
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  have hballAmbient : W.criticalBall ⊆ physical.ambient := by
    intro i hi
    have hiSelected : i ∈ genericNativeHighActivePatternMaxWeightFiber D G c :=
      W.criticalBall_subset_family hi
    have hiFamily : i ∈
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).family := by
      have hfull := genericNativeHighActivePatternMaxWeightFiber_subset D G c
        hiSelected
      exact hfull
    rw [positiveCenterHighPayloadGlobalNormData_family] at hiFamily
    exact (mem_actualGlobalNormIndexFamily_iff S.family physical
      D.globalScale c.1.1).mp hiFamily |>.1
  have hballSource : ∀ i, i ∈ W.criticalBall → i ∈ S.source := by
    intro i hi
    exact hambientSource (hballAmbient hi)
  have hCgap : ∀ i, i ∈ W.criticalBall →
      |projectedTubeGraphC (S.family.tubes i) -
        projectedTubeGraphC (S.family.tubes W.criticalCenter)| ≤
          (radius : Real) / 2 := by
    intro i hi
    apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
    · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
    · exact (G.hbucket i (hballAmbient hi)).trans
        (G.hbucket W.criticalCenter
          (hballAmbient W.criticalCenter_mem_criticalBall)).symm
  have hdistance : ∀ i j,
      W.distance i j = projectedTubePairCoefficientDistance
        (S.family.tubes i) (S.family.tubes j) := by
    intro i j
    rfl
  have hdelta : W.delta = (radius : Real) := by
    rfl
  have hceiling : W.ceiling ≤ 16 := by
    change (16 : Real) ≤ 16
    exact le_rfl
  let haxis := weightedCanonicalCriticalScaleProxy_axisLength
    S W hballSource hCgap hdistance hdelta
  let htransverse := weightedCanonicalCriticalScaleProxy_transverseRadius
    S W (hballSource W.criticalCenter W.criticalCenter_mem_criticalBall)
      hceiling
  refine ⟨haxis, htransverse, ?_⟩
  exact weightedCanonicalCriticalScaleProxy_chart
    S W hballSource hCgap hdistance hdelta

#print axioms exists_genericNativeHighActivePatternMaxWeight_proxyGeometry

end
end Family8Family7GenericNativeHighMaxWeightProxyGeometryV3
