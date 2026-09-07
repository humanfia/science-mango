import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightValueV2
import Family8Grounding.Family8FiniteENNRealMaxWeightFiberV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternMaxWeightNormCommonV1

open Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
open Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
open Family8Family7GenericNativeHighActivePatternMaxWeightValueV2
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Every member of the restricted norm datum has exactly its selected
positive maximal occurrence weight. -/
theorem genericNativeHighActivePatternMaxWeightNormData_common
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0)
    (i : iota)
    (hi : i ∈ (genericNativeHighActivePatternMaxWeightNormData
      D G c hsource).family) :
    (genericNativeHighActivePatternMaxWeightNormData D G c hsource).weight i =
      genericNativeHighActivePatternMaxWeightValue D G c := by
  change genericNativeHighActivePatternOccurrenceWeight D G c i =
    genericNativeHighActivePatternOccurrenceWeight D G c
      (Family8FiniteENNRealMaxWeightIndexV1.maxWeightIndex
        (genericNativeHighFirstHitNormData D c).family
        (genericNativeHighActivePatternOccurrenceWeight D G c)
        (genericNativeHighFirstHitNormData D c).family_nonempty)
  change i ∈ genericNativeHighActivePatternMaxWeightFiber D G c at hi
  exact (Finset.mem_filter.mp hi).2

end

end Family8Family7GenericNativeHighActivePatternMaxWeightNormCommonV1
