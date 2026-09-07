import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightMassV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternPositiveTotalWeightV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7GenericNativeHighOccurrenceWeightMassV1
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

/-- Nonzero active-pattern source mass is exactly nonzero total occurrence
weight on the original canonical norm family. -/
theorem genericNativeHighActivePattern_totalWeight_ne_zero
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0) :
    (∑ i ∈ (genericNativeHighFirstHitNormData D c).family,
      genericNativeHighActivePatternOccurrenceWeight D G c i) ≠ 0 := by
  rw [sum_genericNativeHighActivePatternOccurrenceWeight_eq_source D G c]
  exact hsource

#print axioms genericNativeHighActivePattern_totalWeight_ne_zero

end


end Family8Family7GenericNativeHighActivePatternPositiveTotalWeightV1
