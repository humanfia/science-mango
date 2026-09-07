import Family8Grounding.Family8Family7GenericNativeHighMaxWeightCriticalBallMassV1
import Family8Grounding.Family8Family7ActivePatternLowerBucketFiberMassConnectorV1
import Family8Grounding.Family8Family7LowerBucketGenericNativeBranchCoreV1
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyAverageV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7LowerBucketMaxWeightCriticalBallShadingMassV2

open Submission.Kakeya.ConvexGeometry
open Family8Family7ActivePatternLowerBucketFiberMassConnectorV1
open Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
open Family8Family7GenericNativeHighActivePatternOccurrenceDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighMaxWeightCriticalBallMassV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8WeightedCanonicalCriticalScaleProxyAverageV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! V1 exposed two representation mismatches.  This successor makes the
occurrence-weight projection and subtype shading sum explicit. -/

theorem fibreFloor_mul_activePatternSource_le_familyCard_mul_maxWeightCriticalBallShadingMass
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
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0) :
    let N := genericNativeHighFirstHitNormData D c
    let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
    fibreFloor * volume (genericNativeHighActivePatternSource D G c) ≤
      (N.family.card : ENNReal) *
        (weightedCanonicalCriticalBallShading S W
          (shadingWindowRestriction Y f hfContinuous.measurable
            X hX I hI)).shadingMass := by
  classical
  let N := genericNativeHighFirstHitNormData D c
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  let Ywindow := shadingWindowRestriction Y f hfContinuous.measurable
    X hX I hI
  have hsourceBall :=
    activePatternSource_le_familyCard_mul_maxWeightCriticalBallWeight
      D G c hsource
  have hfloorRaw :=
    fibreFloor_mul_activePatternOccurrenceWeight_le_ballShadingMass
      Y active f hfContinuous.measurable X hX I hI fibreFloor N
      (genericNativeHighFirstHitIncidenceData D G c).shading
      (genericNativeHighActivePatternSource D G c)
      (genericNativeHighActivePatternOccurrenceData D G c)
      W.criticalBall
  have hoccurrence : ∀ i,
      (genericNativeHighActivePatternOccurrenceData D G c).occurrenceWeight i =
        W.weight i := by
    intro i
    rfl
  have hmassEq :
      (weightedCanonicalCriticalBallShading S W Ywindow).shadingMass =
        ∑ i ∈ W.criticalBall, volume (Ywindow.carrier i) := by
    unfold Shading.shadingMass
    simp only [weightedCanonicalCriticalBallShading]
    symm
    exact Finset.sum_subtype _ (fun _i => Iff.rfl) _
  have hfloor : fibreFloor * (∑ i ∈ W.criticalBall, W.weight i) ≤
      (weightedCanonicalCriticalBallShading S W Ywindow).shadingMass := by
    rw [hmassEq]
    simpa only [hoccurrence] using hfloorRaw
  calc
    fibreFloor * volume (genericNativeHighActivePatternSource D G c) ≤
        fibreFloor * ((N.family.card : ENNReal) *
          ∑ i ∈ W.criticalBall, W.weight i) := by
      gcongr
    _ = (N.family.card : ENNReal) *
        (fibreFloor * ∑ i ∈ W.criticalBall, W.weight i) := by
      ac_rfl
    _ ≤ (N.family.card : ENNReal) *
        (weightedCanonicalCriticalBallShading S W Ywindow).shadingMass := by
      gcongr

end

end Family8Family7LowerBucketMaxWeightCriticalBallShadingMassV2
