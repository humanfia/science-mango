import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighOccurrenceWeightMassV1

open Family8Family7ActivePatternOccurrenceWeightV1.ActivePatternOccurrenceData
open Family8Family7GenericNativeHighActivePatternOccurrenceDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-- The generic equal-share occurrence weight retains the exact E2 mass. -/
theorem sum_genericNativeHighActivePatternOccurrenceWeight_eq_source
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    (∑ i ∈ (genericNativeHighFirstHitNormData D c).family,
      genericNativeHighActivePatternOccurrenceWeight D G c i) =
      volume (genericNativeHighActivePatternSource D G c) := by
  exact sum_occurrenceWeight_eq_source
    (genericNativeHighActivePatternOccurrenceData D G c)

#print axioms sum_genericNativeHighActivePatternOccurrenceWeight_eq_source

end

end Family8Family7GenericNativeHighOccurrenceWeightMassV1
