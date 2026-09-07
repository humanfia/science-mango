import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set
open scoped NNReal

namespace Family8Family7GenericNativeHighOccurrencePhysicalV1

open Family8Family7ActivePatternOccurrenceWeightV1
open Family8Family7ActivePatternOccurrenceWeightV1.ActivePatternOccurrenceData
open Family8Family7GenericNativeHighActivePatternOccurrenceDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
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

/-- Every occurrence stays physically active on its exact pattern event. -/
theorem genericNativeHighActivePattern_occurrence_mem_physicalAt
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (p : (genericNativeHighActivePatternOccurrenceData D G c).PatternIndex)
    {i : iota}
    (hi : i ∈
      (genericNativeHighActivePatternOccurrenceData D G c).occurrenceFiber p)
    {x : Real × Real}
    (hx : x ∈ activePatternEvent physical
      (genericNativeHighActivePatternSource D G c) p.1) :
    i ∈ physical.activeAtPoint x := by
  exact occurrence_mem_physicalAt_of_mem_event
    (genericNativeHighActivePatternOccurrenceData D G c) p hi hx

#print axioms genericNativeHighActivePattern_occurrence_mem_physicalAt

end

end Family8Family7GenericNativeHighOccurrencePhysicalV1
