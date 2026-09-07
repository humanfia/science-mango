import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
import Family8Grounding.Family8Family7GenericNativeHighWeightedNormDataV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighWeightedCriticalBallV1
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

/-- The weighted critical-scale datum synchronized with the exact
active-pattern occurrence weight. -/
noncomputable def genericNativeHighActivePatternWeightedNormData
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    WeightedCanonicalNormBallData iota :=
  genericNativeHighWeightedNormData D c
    (genericNativeHighActivePatternOccurrenceWeight D G c)

#print axioms genericNativeHighActivePatternWeightedNormData

end

end Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
