import Family8Grounding.Family8Family7GenericNativeHighWeightedNormDataV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighWeightedCriticalBallSupportV1

open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-- The selected generic weighted critical ball stays in the actual physical
ambient; this is inherited from the canonical norm-family support. -/
theorem genericNativeHighWeightedCriticalBall_subset_physicalAmbient
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.HighCenter) (weight : iota → ENNReal) :
    (genericNativeHighWeightedNormData D c weight).criticalBall ⊆
      physical.ambient := by
  intro i hi
  have hiFamily : i ∈
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).family :=
    (genericNativeHighWeightedNormData D c weight).criticalBall_subset_family
      hi
  rw [positiveCenterHighPayloadGlobalNormData_family] at hiFamily
  exact (mem_actualGlobalNormIndexFamily_iff S.family physical
    D.globalScale c.1.1).mp hiFamily |>.1

#print axioms genericNativeHighWeightedCriticalBall_subset_physicalAmbient

end

end Family8Family7GenericNativeHighWeightedCriticalBallSupportV1
