import Family8Grounding.Family8Family7LowerBucketMaxWeightCriticalBallShadingMassV2
import Family8Grounding.Family8Family7GenericNativeHighMaxWeightProxyGeometryV3
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyAverageV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7LowerBucketMaxWeightCriticalScaleProxyAverageMassV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighMaxWeightProxyGeometryV3
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8Family7LowerBucketMaxWeightCriticalBallShadingMassV2
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalV3
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyAverageV2
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open Family8WeightedCanonicalCriticalScaleProxyShadingV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! V1 omitted the namespace containing the literal window restriction.
This successor keeps the same same-object proxy endpoint. -/

theorem exists_lowerBucketMaxWeightCriticalScaleProxy_averageMass
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (f : Real → Real) (hfContinuous : Continuous f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (fibreFloor : ENNReal)
    (D : LowerBucketNativeBranchCore S Y active f hfContinuous
      X hX I hI fibreFloor)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0)
    (hambientSource : D.physicalDatum.ambient ⊆ S.source) :
    let N := genericNativeHighFirstHitNormData D c
    let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
    let Ywindow := shadingWindowRestriction Y f hfContinuous.measurable
      X hX I hI
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
      affineJacobian (weightedCanonicalCriticalScaleAffineEquiv S W) *
          (fibreFloor * volume
            (genericNativeHighActivePatternSource D G c)) ≤
        (N.family.card : ENNReal) *
          (weightedCanonicalCriticalScaleProxyShading
            S W Ywindow haxis htransverse).shadingMass ∧
      (weightedCanonicalCriticalScaleProxyShading
          S W Ywindow haxis htransverse).averageMultiplicity =
        (weightedCanonicalCriticalBallShading S W Ywindow).averageMultiplicity := by
  let N := genericNativeHighFirstHitNormData D c
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  let Ywindow := shadingWindowRestriction Y f hfContinuous.measurable
    X hX I hI
  obtain ⟨haxis, htransverse, hchart⟩ :=
    exists_genericNativeHighActivePatternMaxWeight_proxyGeometry
      D G c hsource hambientSource
  refine ⟨haxis, htransverse, hchart, ?_, ?_⟩
  · have hmass :=
      fibreFloor_mul_activePatternSource_le_familyCard_mul_maxWeightCriticalBallShadingMass
        Y active f hfContinuous X hX I hI fibreFloor D G c hsource
    have hproxyMass :=
      weightedCanonicalCriticalScaleProxyShading_shadingMass
        S W Ywindow haxis htransverse
    calc
      affineJacobian (weightedCanonicalCriticalScaleAffineEquiv S W) *
          (fibreFloor * volume
            (genericNativeHighActivePatternSource D G c)) ≤
        affineJacobian (weightedCanonicalCriticalScaleAffineEquiv S W) *
          ((N.family.card : ENNReal) *
            (weightedCanonicalCriticalBallShading S W Ywindow).shadingMass) := by
        gcongr
      _ = (N.family.card : ENNReal) *
          (affineJacobian (weightedCanonicalCriticalScaleAffineEquiv S W) *
            (weightedCanonicalCriticalBallShading S W Ywindow).shadingMass) := by
        ac_rfl
      _ = (N.family.card : ENNReal) *
          (weightedCanonicalCriticalScaleProxyShading
            S W Ywindow haxis htransverse).shadingMass := by
        rw [hproxyMass]
  · exact weightedCanonicalCriticalScaleProxyShading_averageMultiplicity
      S W Ywindow haxis htransverse

end

end Family8Family7LowerBucketMaxWeightCriticalScaleProxyAverageMassV2
