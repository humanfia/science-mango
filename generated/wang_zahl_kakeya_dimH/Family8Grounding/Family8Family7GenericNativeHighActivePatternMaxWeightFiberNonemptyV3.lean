import Family8Grounding.Family8Family7ActivePatternPositiveMaxWeightFiberV2
import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternMaxWeightFiberNonemptyV3

open Family8Family7ActivePatternOccurrenceWeightV1
open Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
open Family8Family7GenericNativeHighActivePatternOccurrenceDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Positive active-pattern source mass makes the literal maximal-weight
fibre nonempty. -/
theorem genericNativeHighActivePatternMaxWeightFiber_nonempty
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0) :
    (genericNativeHighActivePatternMaxWeightFiber D G c).Nonempty := by
  let P := genericNativeHighActivePatternOccurrenceData D G c
  have H := Family8Family7ActivePatternPositiveMaxWeightFiberV2.ActivePatternOccurrenceData.positiveMaxWeightFiberData_of_source_ne_zero P hsource
  change
    (Family8FiniteENNRealMaxWeightFiberV1.maxWeightFiber
      (genericNativeHighFirstHitNormData D c).family
      P.occurrenceWeight
      (genericNativeHighFirstHitNormData D c).family_nonempty).Nonempty
  exact H.fiber_nonempty

end

end Family8Family7GenericNativeHighActivePatternMaxWeightFiberNonemptyV3
