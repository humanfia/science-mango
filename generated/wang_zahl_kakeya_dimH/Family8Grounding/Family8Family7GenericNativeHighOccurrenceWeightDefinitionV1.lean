import Family8Grounding.Family8Family7GenericNativeHighActivePatternOccurrenceDataV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1

open Family8Family7ActivePatternOccurrenceWeightV1.ActivePatternOccurrenceData
open Family8Family7GenericNativeHighActivePatternOccurrenceDataV1
open Family8Family7GenericNativeHighGeometryV1
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

/-- Equal-share active-pattern occurrence weight on the original tube index. -/
noncomputable def genericNativeHighActivePatternOccurrenceWeight
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (i : iota) : ENNReal :=
  (genericNativeHighActivePatternOccurrenceData D G c).occurrenceWeight i

#print axioms genericNativeHighActivePatternOccurrenceWeight

end

end Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
