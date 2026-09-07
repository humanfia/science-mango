import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightMassV1
import Family8Grounding.Family8Family7WeightedCriticalBallMassRetentionV2
import Family8Grounding.Family8FiniteENNRealMaxWeightIndexDominatesV1
import Family8Grounding.Family8FiniteENNRealMaxWeightIndexMemV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighMaxWeightCriticalBallMassV1

open Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
open Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7GenericNativeHighOccurrenceWeightMassV1
open Family8Family7WeightedCriticalBallMassRetentionV2
open Family8FiniteENNRealMaxWeightFiberV1
open Family8FiniteENNRealMaxWeightIndexDominatesV1
open Family8FiniteENNRealMaxWeightIndexMemV1
open Family8FiniteENNRealMaxWeightIndexV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! The exact active-pattern mass is retained by the same restricted
maximal-weight critical ball with only the original norm-family cardinality
loss. -/

theorem activePatternSource_le_familyCard_mul_maxWeightCriticalBallWeight
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0) :
    let N := genericNativeHighFirstHitNormData D c
    let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
    volume (genericNativeHighActivePatternSource D G c) ≤
      (N.family.card : ENNReal) *
        ∑ i ∈ W.criticalBall, W.weight i := by
  let N := genericNativeHighFirstHitNormData D c
  let weight := genericNativeHighActivePatternOccurrenceWeight D G c
  let imax := maxWeightIndex N.family weight N.family_nonempty
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  have himaxFamily : imax ∈ N.family := maxWeightIndex_mem _ _ _
  have himaxW : imax ∈ W.family := by
    change imax ∈ maxWeightFiber N.family weight N.family_nonempty
    rw [maxWeightFiber, Finset.mem_filter]
    exact ⟨himaxFamily, rfl⟩
  have hmaxBall : weight imax ≤
      ∑ i ∈ W.criticalBall, W.weight i := by
    have h := weight_le_criticalBallWeight W himaxW
    exact h
  have hsum : (∑ i ∈ N.family, weight i) ≤
      (N.family.card : ENNReal) * weight imax := by
    have H := Finset.sum_le_card_nsmul N.family weight (weight imax)
      (fun i hi => weight_le_maxWeightIndex N.family weight
        N.family_nonempty hi)
    simpa only [nsmul_eq_mul] using H
  calc
    volume (genericNativeHighActivePatternSource D G c) =
        ∑ i ∈ N.family, weight i := by
      symm
      exact sum_genericNativeHighActivePatternOccurrenceWeight_eq_source
        D G c
    _ ≤ (N.family.card : ENNReal) * weight imax := hsum
    _ ≤ (N.family.card : ENNReal) *
        ∑ i ∈ W.criticalBall, W.weight i := by
      gcongr

end

end Family8Family7GenericNativeHighMaxWeightCriticalBallMassV1
