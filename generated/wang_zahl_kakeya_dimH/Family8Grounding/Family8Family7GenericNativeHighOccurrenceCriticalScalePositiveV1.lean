import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped NNReal

namespace Family8Family7GenericNativeHighOccurrenceCriticalScalePositiveV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
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

/-- Positivity of the occurrence-weighted selected critical scale. -/
theorem genericNativeHighActivePatternCriticalScale_pos
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    0 < (genericNativeHighActivePatternWeightedNormData D G c).criticalScale :=
  (genericNativeHighActivePatternWeightedNormData D G c).delta_pos.trans_le
    (genericNativeHighActivePatternWeightedNormData D G c).criticalScale_bounds.1

#print axioms genericNativeHighActivePatternCriticalScale_pos

end

end Family8Family7GenericNativeHighOccurrenceCriticalScalePositiveV1
