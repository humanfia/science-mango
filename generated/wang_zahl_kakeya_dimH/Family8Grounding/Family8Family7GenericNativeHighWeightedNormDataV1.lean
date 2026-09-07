import Family8Grounding.Family8Family7GenericNativeHighGeometryV1
import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighWeightedNormDataV1

open Family8Family7NativeHighWeightedCriticalBallV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-!
# Arbitrary weighted norm input over a generic native-high core

This is the field-for-field weighted adapter only.  Critical-ball support,
occurrence specialization, and retention are isolated in successors.
-/

noncomputable def genericNativeHighWeightedNormData
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.HighCenter) (weight : iota → ENNReal) :
    WeightedCanonicalNormBallData iota := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  exact
    { family := N.family
      distance := N.distance
      weight := weight
      delta := N.delta
      ceiling := N.ceiling
      exponent := N.exponent
      family_nonempty := N.family_nonempty
      self_le_delta := N.self_le_delta
      delta_pos := N.delta_pos
      delta_le_ceiling := N.delta_le_ceiling
      exponent_nonneg := N.exponent_nonneg }

#print axioms genericNativeHighWeightedNormData

end

end Family8Family7GenericNativeHighWeightedNormDataV1
